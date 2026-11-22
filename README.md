# Blast Radius entry

Picks the sqlglot tests a patch can break.

`selector.py` reads each patch, works out which functions, class bodies or
fixtures it touches in sqlglot at the pinned commit
(`eb11aec4be8cb2122afe713a4816662c3f0fb2fa`), and selects the tests that reach
them according to `map.pkl`. It runs no tests and looks nothing up by patch.

`map.pkl` is built once from the pinned commit only:

- per-test line coverage (coverage.py dynamic contexts, one process per test file),
- lines run outside a test (imports, class setup), per test file,
- which tests use which dialect, parser, generator and expression classes,
- which tests open which repository files (fixtures, sources read as text),
- sqlglot's own sources and static import graph.

Libraries used to build the map: coverage.py, pytest and the packages in the
kit's `requirements.lock`. The selector itself uses only the standard library.

Released under the MIT License.
