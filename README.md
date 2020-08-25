[![Workflow Status](https://github.com/enarx/lset/workflows/test/badge.svg)](https://github.com/enarx/lset/actions?query=workflow%3A%22test%22)
[![Average time to resolve an issue](https://isitmaintained.com/badge/resolution/enarx/lset.svg)](https://isitmaintained.com/project/enarx/lset "Average time to resolve an issue")
[![Percentage of issues still open](https://isitmaintained.com/badge/open/enarx/lset.svg)](https://isitmaintained.com/project/enarx/lset "Percentage of issues still open")
![Maintenance](https://img.shields.io/badge/maintenance-activly--developed-brightgreen.svg)

# lset

This crate contains types for measuring linear sets by either the end
points (`Line`) or by a starting point and the number of elements (`Span`).

In the interest of zero-cost abstractions, all methods are always inlined
for maximum compiler optimization. Thus, you only pay for the conversions
that are actually used.

License: Apache-2.0
