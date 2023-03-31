# coq-synthesis
Coq plugin for proof generation and next tactic prediction.

## Prerequisites

You'll need to install `git`, `opam`, `rustup`, `graphviz`, `libgraphviz-dev`,
`python3.10`, `python3.10-dev` and `python3.10-pip` to run Proverbot, which is the ML theorem prover that this plugin uses.


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

Once that's finished, you're ready to start running the tool!

To try the tool, open a `.v` file, (to import the plugin correctly, run `dune coq top --toplevel coqide path/to/.v/file`) and write this on line 1 of the file:

`Require Import SynthesisPlugin.`

You will also have to provide the path to proverbot:

`Set Proverbot Path path/to/proverbot`,

which the setup script clones one level above the current directory

and the current file path:

`Set Current File Path path/to/this/.v/file`

To generate the proof for a theorem, start the proof with `Proof.`, and in the proof body, call the command `RunProverbot`.