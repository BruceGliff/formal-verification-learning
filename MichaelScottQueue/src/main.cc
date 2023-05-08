#include "MichaelScottQueue.hpp"

#include <cstdlib>
#include <thread>
#include <vector>

std::atomic<int> MsgCount{0};
std::atomic<int> MsgRead{0};

using QType = MSQueue<int>;

void read(QType &Q, int Msgs) {
  while (MsgRead < Msgs) {
    if (auto x = Q.dequeue()) {
      ++MsgRead;
    }
  }
}

void write(QType &Q, int Msgs) {
  while (MsgCount < Msgs) {
    auto val = MsgCount.load();
    if (MsgCount.compare_exchange_strong(val, val + 1)) {
      Q.enqueue(val);
    }
  }
}

int main(int argc, char *argv[]) {

  // Default Msgs value
  int Msgs = 100;
  int Readers = 3;
  int Writers = 2;
  if (argc >= 2)
    Msgs = strtol(argv[1], nullptr, 10);
  if (argc >= 3)
    Readers = strtol(argv[2], nullptr, 10);
  if (argc >= 4)
    Writers = strtol(argv[3], nullptr, 10);

  if (!(Msgs > 0 && Readers > 0 && Writers > 0)) {
    std::cerr << "Wrong args\n";
    return -1;
  }

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
          pool.emplace_back(read, std::ref(Q), Msgs);
        }
      } else {
        if (WritersPl < Writers) {
          WritersPl++;
          pool.emplace_back(write, std::ref(Q), Msgs);
        }
      }
      ++i;
    }
  }

  return 0;
}