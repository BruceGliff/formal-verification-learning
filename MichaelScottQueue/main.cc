#include "MichaelScottQueue.hpp"

#include <thread>
#include <vector>

std::atomic<int> MsgCount{0};
std::atomic<int> MsgRead{0};
constexpr int Msgs = 500;
constexpr int Readers = 2;
constexpr int Writers = 3;

using QType = MSQueue<int>;

void read(QType &Q) {
  while (MsgRead < Msgs) {
    if (auto x = Q.dequeue()) {
      ++MsgRead;
    }
  }
}

void write(QType &Q) {
  while (MsgCount < Msgs) {
    auto val = MsgCount.load();
    if (MsgCount.compare_exchange_strong(val, val + 1)) {
      Q.enqueue(val);
    }
  }
}

int main() {

  int ReadersPl = 0;
  int WritersPl = 0;
  MSQueue<int> Q;

  {
    std::vector<std::jthread> pool;
    int i = 0;
    while (ReadersPl + WritersPl < Readers + Writers) {
      if (i % 2) {
        if (ReadersPl < Readers) {
          ReadersPl++;
          pool.emplace_back(read, std::ref(Q));
        }
      } else {
        if (WritersPl < Writers) {
          WritersPl++;
          pool.emplace_back(write, std::ref(Q));
        }
      }
      ++i;
    }
  }

  return 0;
}