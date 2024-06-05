# coq-synthesis
Coq-synthesis is a Coq plugin for proof generation, decompilation and next tactic prediction.

## Setup

### Prerequisites

You'll need to install `git`, `opam`, `rustup`, `graphviz`, `libgraphviz-dev`,
`python3.10`, `python3.10-dev` and `python3.10-pip` to run Proverbot, which is the ML theorem prover that this plugin uses (Proverbot will be installed by the setup script for the plugin).


The first thing you'll need to do is clone the repository (download the code).

I recommend that you do this over ssh. Open a terminal (windows users
can use "Bash on Ubuntu on Windows"), move to the directory you want
to work in, and run:

```
git clone git@github.com:agrarpan/coq-synthesis.git
```

That should give you a new folder called `coq-synthesis` with all the
code inside. Move into this new directory:

```
cd coq-synthesis
```

And run this command to install the dependencies, which will download proverbot and run the setup for it.

```
make setup
```

This step will take a while, and might involve having to type `y` a
few times.

After the script finishes running, run `dune build` inside the `coq-synthesis directory` (Make sure to change the proverbot and current file paths in `Test.v` according to the instructions below).

Once that's finished, you're ready to start running the tool!

### Troubleshooting problems during setup

Depending on your OS, sourcing of the conda environment can sometimes fail. You might have to manually load the virtual environment created by the script (called synth).

If you see an error message near the bottom that says:
```
pygraphviz/graphviz_wrap.c:2711:10: fatal error: graphviz/cgraph.h: No such file or directory
 2711 | #include "graphviz/cgraph.h"
      |          ^~~~~~~~~~~~~~~~~~~
compilation terminated.
error: command 'x86_64-linux-gnu-gcc' failed with exit status 1
```
then python needs help finding your graphviz installation. Check out this github issue: https://github.com/pygraphviz/pygraphviz/issues/155, and possibly this one: https://github.com/pypa/setuptools/issues/2740

## Using the plugin.

To try the tool, open a `.v` file, (to import the plugin correctly, run `dune coq top --toplevel coqide path/to/.v/file`) and write this on line 1 of the file (It is necessary for this to be on line 1 because of the way the plugin parses files):

`Require Import SynthesisPlugin.`

(For some reason, this does not open the file in coqide, and I have to manually open the file from the coqide menu. If you know how to fix this, please let us know).

You will also have to provide the path to proverbot:

`Set Proverbot Path path/to/proverbot/`,

which the setup script clones one level above the current directory

and the current file path:

`Set Current File Path path/to/this/.v file`


### Commands introduced by this plugin.

This plugin introduces 3 new commands: 
1) RunProverbot2, which tries to synthesize a proof for you. It has to be called after starting a proof.
2) Decompile term_name, which takes the name of a term and tries to decompile it. It has to be called after the term has been declared. We're adding more functionality to this currently.
3) PredictTactic, which predicts the top 5 tactics to be used at the current proof state. It has to be called after starting a proof.

To generate the proof for a theorem, start the proof with `Proof.`, and in the proof body, call the command `RunProverbot2` followed by `Admitted`. You can optionally provide a partial proof before calling the `RunProverbot2` tactic, which can be used to guide the proof search. If Proverbot succeeds in proving the theorem, it will open up a new browser window with the search tree it explored.

For example, in file theories/Test.v, if we run RunProverbot2 right after starting the proof, Proverbot does not manage to find a proof for the theorem. If we examine the search tree, we can see that it attempted to induct on the lists, but never on the inductive hypothesis itself.
We can guide the search in the right direction by using `induction 1` on the line before we call `RunProverbot2` (this tactic inducts on the first unnamed hypothesis). Provebot then manages to prove the theorem! 

To decompile a term, you can call `Decompile term_name` at any point after the term has been declared.

To predict the best 5 tactics at any point in a proof, you can call `PredictTactic`.
