tla_tools
=========

Put these scripts on your PATH and they should help you run the [TLA+ Tools](http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html)

Note that you may need to modify `lib/common` with the appropriate paths.

Also, from what I can tell all of these tools expect to be run in the same directory as the input files.

Example:

``````
joe@hostname ~/src/some/path $ tlc2 blah.tla

``````


### Examples

`````
joe@hostname ~/src/tla_tools/examples $ pcal-trans 3pc.tla
pcal.trans Version 1.8 of 2 Apr 2013
Parsing completed.
Translation completed.
New file 3pc.tla written.
New file 3pc.cfg written.
joe@hostname ~/src/tla_tools/examples $ tlc2 3pc.tla
TLC2 Version 2.05 of 23 July 2013
Running in Model-Checking mode.
Parsing file 3pc.tla
Parsing file /usr/local/tla/tla2sany/StandardModules/TLC.tla
Parsing file /usr/local/tla/tla2sany/StandardModules/Naturals.tla
Parsing file /usr/local/tla/tla2sany/StandardModules/Sequences.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TLC
Semantic processing of module 3pc
Starting... (2014-12-09 17:34:13)
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.8E-13
  based on the actual fingerprints:  val = 1.4E-13
3937 states generated, 1280 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 31.
Finished. (2014-12-09 17:34:14)
`````