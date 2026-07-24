# Formalizing the Linux eBPF Core ISA: A Mechanized Operational Semantics and Real-world Application

This repository extends the mechanized Linux eBPF semantics with a Coq formalization of tracked numbers (tnums) and soundness proofs for the tnum operations used by the eBPF verifier.

## Code Structure

- `semantics/`: the Linux eBPF semantics submodule, including the Coq theories, executable validator, and Linux execution traces
- `tnum/`: the mathematical tnum model, executable CompCert-integer model, operation-level soundness proofs, and integration with the eBPF ALU semantics

The public Coq namespaces are:

- `semantics/theories/` → `bpf.semantics`
- `tnum/` → `bpf.tnum`

## Install

Use opam to install Coq 8.19.0, CompCert, Dune, Zarith, and Yojson.

```shell
opam switch create linux-ebpf --empty
opam pin coq 8.19.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-compcert dune zarith yojson
```

Initialize the semantics submodule after cloning:

```shell
git submodule update --init --recursive
```

## Build

The command `make` first builds the semantics submodule and then checks every Coq file under `tnum/`.

```shell
make -j
```

Use the following command to remove generated Coq, OCaml, and Dune artifacts from both the main repository and the semantics submodule:

```shell
make clean
```

## Semantics Validation

The top-level Makefile forwards the validation targets to the semantics
submodule:

```shell
make validation1 # validate the test_progs execution traces
make validation2 # validate the test_bpf execution traces
```

To build the extracted OCaml validator without running traces:

```shell
make validation
```

## Link to Paper and Source Files

```text
.
├── semantics/                         # linux-ebpf-semantics submodule
│   ├── theories/
│   │   ├── ebpfState.v                # eBPF state (Section 3.1)
│   │   ├── ebpfSyntax.v               # eBPF syntax (Section 3.2, Fig. 4)
│   │   └── ebpfBinSem.v               # eBPF semantics (Section 3.3)
│   ├── validator/
│   │   ├── Validation.v               # reference interpreter (Section 4.2)
│   │   ├── Extraction.v               # OCaml extraction entry point
│   │   └── main.ml                    # validation CLI (Section 4.1, Fig. 8)
│   └── trace/
│       ├── test_progs/                 # Linux BPF selftest traces
│       └── test_bpf/                   # Linux BPF interpreter test traces
└── tnum/
    ├── Zmore.v                         # auxiliary integer and bitwise lemmas
    ├── tnumZ.v                         # mathematical tnum model over Coq Z
    ├── tnumZ_inv.v                     # tnum invariants
    ├── tnumZ_add_sound.v               # addition soundness
    ├── tnumZ_not_sound.v               # bitwise-not soundness
    ├── tnumZ_sub_sound.v               # subtraction soundness
    ├── tnumZ_shift_sound.v             # shift soundness
    ├── tnumZ_mod_eq.v                  # modular-equivalence lemmas
    ├── tnumZ_mul_sound.v               # multiplication soundness
    ├── tnumZ_udiv_sound.v              # unsigned-division soundness
    ├── tnumZ_umod_sound.v              # unsigned-modulo soundness
    ├── tnum.v                          # executable tnum model over CompCert Int64
    ├── tnum_proof.v                    # bridge between tnumZ and Int64 models
    └── tnum_soundness.v                # integration with eBPF ALU semantics
```

## Code Statistics

Install `cloc` if OCaml line counts are required:

```shell
sudo apt-get install cloc
```

Run the statistics targets from the repository root:

```shell
make tnumcode       # tnum Coq code size using coqwc
make bpfcode        # eBPF semantics Coq code size using coqwc
make validationcode # handwritten OCaml validator size using cloc
```

## Proof Status

All active proofs are complete. The textual `Admitted` in `tnum_proof.v` is inside commented-out legacy code.

The kernel patch and eBPF observer are provided in a separate Linux repository; its README gives their paths and execution instructions.
