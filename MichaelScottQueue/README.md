C++ implementation of Michael-Scott queue and LTL trace verification.

Requirements: `C++20, spot and atomic libs`

Build and run:
```
cmake -S .
make
./MichaelScottQueue [Number of messages] [Number of readers] [Number of writers]
```

Model build with formulas in `LTL.fml` file.

Verification run:
```
python ./verify.py [trace from queue] [model file]
```
There are equal terms in project: `store == enqueue == write` `load == dequeue == read`
