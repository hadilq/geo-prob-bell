# Geometrical Probability of Bell's Theorem — formal companion

Lean 4 + Mathlib development of the algebra in the post
[*Geometrical Probability of Bell's Theorem*](https://hadilq.com/posts/geometrical-probability-of-bell/).

Everything the post asserts algebraically is stated and proved here: the
chart-change dial and its group law, the master formula, the Sleeping Beauty
warm-up, the CHSH transformation law, the preservation of the local bound, and
the four thresholds.

Nothing quantum-mechanical is assumed anywhere. Tsirelson's `2√2` enters at
exactly one point, as the hypothesis `hT : |chsh E| ≤ 2 * Real.sqrt 2` of
`chsh_bound`. If you want to know what the development depends on, that
hypothesis is the whole list.

## Build

### With Nix

```sh
nix develop      # or `direnv allow`, the .envrc is a one-liner
make setup       # fetch Mathlib, pin its toolchain, pull its prebuilt oleans
make build       # elaborate every file — this is what "the proofs check" means
```

The flake gives you [`elan`](https://github.com/leanprover/elan), not a
Nix-pinned Lean. That is deliberate: Mathlib builds against exactly one Lean
version, so `lean-toolchain` is the single source of truth and elan reads it.
A pure-Nix Mathlib build would rebuild Mathlib from source and throw away the
upstream olean cache, which costs hours instead of minutes.

`ELAN_HOME` is set to `./.elan` inside the shell, so nothing is written to your
home directory.

### Without Nix

Install [`elan`](https://github.com/leanprover/elan), then:

```sh
make setup
make build
```

### About `lean-toolchain`

It ships as `leanprover/lean4:stable` so that elan can resolve *something*
before Mathlib has been fetched. `make setup` runs `make sync`, which
overwrites it with the exact toolchain Mathlib asks for. Commit the result —
after the first `make setup` this repo is pinned, and `lake-manifest.json`
pins the Mathlib commit alongside it.

If `make build` fails with a toolchain mismatch after a `lake update`, run
`make sync && lake exe cache get && make build`.

## Layout

| Module | Post section | Contents |
|---|---|---|
| `GeoProbBell/Mixer.lean` | §1, §6 | the dial, the group law, stochasticity |
| `GeoProbBell/Master.lean` | §6 | the master formula, the contraction lemma |
| `GeoProbBell/SleepingBeauty.lean` | §1 | `P_H(μ)`, its endpoints, `S_SB(μ) = μ` |
| `GeoProbBell/Product.lean` | §3, §9 | the product chart, the wing-wise dial |
| `GeoProbBell/CHSH.lean` | §5, §6 | `S` under a chart change, the local bound |
| `GeoProbBell/Thresholds.lean` | §7–§9 | the walls |

The dial is parameterised by an arbitrary reference distribution `u`, not just
the uniform one. The uniform `u ≡ 1/N` of the post is `unif` in
`SleepingBeauty.lean`. Carrying `u` around keeps every proof in `Mixer.lean`
and `Master.lean` free of division, which is why the group law is a one-line
ring identity.

## What is proved

**The dial** (`Mixer.lean`)

| Name | Statement |
|---|---|
| `sum_mix` | the dial preserves total mass |
| `mix_nonneg` | it preserves nonnegativity for `0 ≤ μ ≤ 1` |
| `mix_mix` | `M(μ) M(ν) = M(μν)` |
| `mix_one` | `M(1) = I` |
| `mix_inv` | `M(μ)⁻¹ = M(1/μ)` for `μ ≠ 0` |
| `mix_zero` | `M(0)` collapses everything onto the reference |

**The master formula** (`Master.lean`)

| Name | Statement |
|---|---|
| `pair_mix`, `master` | Proposition 1: `E' = μ E + (1-μ)⟨w,u⟩` |
| `pair_adj` | moving the dial onto the readout is the same computation |
| `adj_le` | Proposition 2, the contraction lemma |

**Sleeping Beauty** (`SleepingBeauty.lean`)

| Name | Statement |
|---|---|
| `heads` | `P_H(μ) = μ/2 + (1-μ)/n` |
| `heads_closed` | `= (μ(n-2)+2)/(2n)` |
| `heads_endpoints` | `1/2` at `μ=1`, `1/n` at `μ=0` |
| `contrast` | `S_SB(μ) = μ` |
| `mean_unif` | the readout mean `c_n s` of §8 |

**The product chart** (`Product.lean`)

| Name | Statement |
|---|---|
| `prod_dist` | a product of distributions is a distribution |
| `pair_prod` | `ω̄ = v̄_A v̄_B` |
| `wing_pair` | the wing-wise dial, with its two cross terms |
| `wing_pair_unbiased` | `E' = μ² E + (1-μ)² v̄_A v̄_B` |

**CHSH** (`CHSH.lean`)

| Name | Statement |
|---|---|
| `chsh_affine` | `S' = μ S + 2(1-μ) ω̄` |
| `chsh_local_preserved` | a chart change maps local models to local models, so the bound `2` does not move |
| `chsh_bound` | the boxed inequality of §8, from Tsirelson as a hypothesis |

**The walls** (`Thresholds.lean`)

| Name | Threshold |
|---|---|
| `wall_unvalued` | `1/√2 ≈ 0.7071`, the depolarising visibility threshold |
| `wall_some` | `μ₋ = (1-q)/(√2-q)` — some observer sees a violation |
| `wall_every` | `μ₊ = (1+q)/(√2+q)` — every observer sees one |
| `wall_every_one`, `wall_some_one` | the window becomes `(0, 2(√2-1)]` as `q → 1` |
| `wall_wing` | the wing-wise quadratic |
| `wall_wing_unvalued` | `2^(-1/4) ≈ 0.8409` |
| `wall_wing_valued` | `2(√2-1) ≈ 0.8284`, the Garg–Mermin detection-efficiency threshold |

The thresholds are stated as `iff`s in a division-free form, so each one can be
checked by eye against the inequality it came from.

## Citing

```
@misc{hadilq2026GeoProbBellLean,
    author = {{Hadi Lashkari Ghouchani}},
    title  = {Geometrical Probability of Bell's Theorem --- formal companion},
    year   = {2026},
    note   = {Lean 4 development, \url{https://gitlab.com/hadilq/geo-prob-bell}},
}
```
