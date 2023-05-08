#include <atomic>
#include <iostream>
#include <optional>

template <class T> class MSQueue {
  // Forward declaration
  struct node_t;

  struct pointer_t {
    node_t *ptr{nullptr};
    unsigned count{0u};
  };

  struct node_t {
    T value{};
    std::atomic<pointer_t> next{};
  };

  std::atomic<pointer_t> Head;
  std::atomic<pointer_t> Tail;

public:
  // default constructor
  MSQueue() {
    node_t *pNode = new node_t;
    Head.store(pointer_t{pNode});
    Tail.store(pointer_t{pNode});
  }
  ~MSQueue() {
    auto ptr = Head.load();
    delete ptr.ptr;
  }

  void enqueue(T const &t) {
    node_t *pNode = new node_t;
    pNode->value = t;

    while (true) {
      // Read Tail.ptr and Tail.count together
      pointer_t tail(Tail);

      bool nNullTail = (tail.ptr == nullptr);
      // Read next ptr and count fields together
      pointer_t next{// ptr
                     (nNullTail) ? nullptr : tail.ptr->next.load().ptr,
                     // count
                     (nNullTail) ? 0 : tail.ptr->next.load().count};

      if (tail.count == Tail.load().count && tail.ptr == Tail.load().ptr) {
        if (next.ptr == nullptr) {
          if (tail.ptr->next.compare_exchange_strong(
                  next, pointer_t{pNode, next.count + 1})) {
            std::cout << "Store\n";
            break;
          }
        } else
          Tail.compare_exchange_strong(tail,
                                       pointer_t{next.ptr, tail.count + 1});
      }
    }
  }

  std::optional<T> dequeue() {
    pointer_t head = Head;
    T t{};

    while (true) {
      head = Head;
      pointer_t tail(Tail);

      if (head.ptr == nullptr)
        return {};

      pointer_t next(head.ptr->next);

      if (head.count == Head.load().count && head.ptr == Head.load().ptr) {
        if (head.ptr == tail.ptr) {
          if (next.ptr == nullptr)
            return {};
          Tail.compare_exchange_strong(tail,
                                       pointer_t{next.ptr, tail.count + 1});
        } else {
          t = next.ptr->value;
          if (Head.compare_exchange_strong(
                  head, pointer_t{next.ptr, head.count + 1})) {
            std::cout << "Load\n";
            break;
          }
        }
      }
    }

    // It is now safe to free the old dummy node
    delete head.ptr;

    return t;
  }
};