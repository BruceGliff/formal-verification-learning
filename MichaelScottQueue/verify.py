import spot
import sys

def check(current : int, nxt : int, file) -> bool:
  aut = spot.automaton(file)
  for s in range(aut.num_states()):
    for t in aut.out(s):
      if int(t.src) == current and int(t.dst) == nxt:
        return True
  return False

# ./verify.py trace.log model.hoa
assert(len(sys.argv) == 3)
model_file = sys.argv[2]

def parseTrace(tr) -> int:
  if 'store' in tr:
    return 0
  if 'load' in tr:
    return 1
  raise RuntimeError('unknown state')


trace = open(sys.argv[1], "r").readlines()
counters = [0, 0]
current = parseTrace(trace[0])

# first should be only store.
assert(current == 0)
counters[current] += 1;

for state in trace[1:]:
  state = parseTrace(state)
  counters[state] += 1;
  assert(check(current, state, model_file) == True)
  current = state

# first should be only load.
assert(current == 1)
# counters of store and load are equal.
assert(counters[0] == counters[1])