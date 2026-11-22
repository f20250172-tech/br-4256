# Blast Radius entry

Picks the sqlglot tests a patch can break.

`selector.py` reads each patch, works out which functions, class bodies or
fixtures it touches in sqlglot at the pinned commit
(`eb11aec4be8cb2122afe713a4816662c3f0fb2fa`), and selects the tests that reach
them according to `map.pkl`. It runs no tests and looks nothing up by patch.

`map.pkl` is built once from the pinned commit only:

- per-test line coverage (coverage.py dynamic contexts, one process per test
  file), taken four ways so that one-off effects can be told apart: a cold run,
  the same in reverse test order, a run with every sqlglot module imported
  first, and a run with every dialect also exercised first,
- which lines run when sqlglot's modules are imported,
- lines run outside a test (imports, class setup), per test file,
- which tests use which dialect, parser, generator and expression classes,
- which tests open which repository files (fixtures, sources read as text),
- sqlglot's own sources and static import graph.

How a change is read: an edit inside a function selects the tests that reach
the edited statement; an edit that runs at import (module or class level, or a
function called while a module is imported) selects every test that uses that
module or class; an edit that leaves the syntax tree unchanged selects only
tests that read the file as text; fixtures select the tests that open them.

Libraries used to build the map: coverage.py, pytest and the packages in the
kit's `requirements.lock`. The selector itself uses only the standard library.

Released under the MIT License.
