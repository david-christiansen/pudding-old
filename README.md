Pudding
=========

[![Build Status](https://travis-ci.org/david-christiansen/pudding.svg?branch=master)](https://travis-ci.org/david-christiansen/racket-refiners)
[![Coverage Status](https://coveralls.io/repos/github/david-christiansen/pudding/badge.svg?branch=master)](https://coveralls.io/github/david-christiansen/racket-refiners?branch=master)

Pudding is a proof assistant under development at Indiana University, deeply integrated with the Racket programming language.

Status
------

Pudding is currently incomplete, and cannot yet be used to prove anything.

Installation Instructions
-------------------------

Most of Pudding's dependencies are available on the Racket package server. There is one significant exception, which is a library of GUI components which has not yet had an official release.

First, clone [the GUI components repository](https://github.com/david-christiansen/racket-presentation-gui). In the checked-out directory, run:

```
.../racket-presentation-gui$ raco pkg install -n presentations
```

Once that's done, check out this repository. To test the GUI, run:

```
.../pudding$ racket presentation-gui.rkt
```

To test code generation, run the files in the `demo/` subdirectory.


Web Site
--------

The official Pudding Web site is at [http://pudding-prover.org](http://pudding-prover.org).
