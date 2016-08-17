This directory contains the tests that, for whatever reason, cannot be
part of a test submodule.

In particular, the resource tests need to be separated, because
otherwise raco will not run them in isolated contexts. The current
strategy prevents interference.
