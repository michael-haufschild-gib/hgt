# HB: original native form-domain admission

Stage: 3-formalized. The literal untruncated native remainder's double time primitive belongs to the original joint form domain through its original value embedding. Complete operator identification, physical-current cancellation and RH remain open.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Exact theorem

`nativeJointTimePrimitive_form_admission` proves, for every `q : XiZeroCopy`, complex `s` and `amplitude`, and real `t`,

```
exists v : jointDomain,
  jointEmbedding v = L2(nativeJointTimePrimitiveField q s amplitude t).
```

Here L2 denotes the actual `MemLp.toLp` class in the original radial/modular product measure. The target is the already defined literal native field. The theorem adds no domain, regularity, mixed derivative, frequency-chamber or global-energy hypothesis. All construction obligations are discharged by proved native results. No numerical result or new axiom enters the proof.

## Admitted finite cutoffs

The [radial smoothing construction](hb-native-radial-mollification.md) admits every actual cusp-cutoff graph `v_n`. Its components are the original value, projected radial derivative, and both sech-weighted angular derivatives. Normalized bump convolution first removes the radial interior regularity obstruction. Its value embedding commutes with convolution and its actual derivative is identified before taking limits. The audited endpoint estimates remove the Dirichlet cutoff. Thus every `v_n` lies in the original closed joint form domain.

## Uniform original form bound

The original Bochner/product isometry preserves each component norm. The angular energy element is the original frame graph of the actual cusp-cutoff core field. This identifies the value norm and both derivative norms with their literal iterated squared integrals. The original projected radial derivative is the admitted literal derivative, so its norm is exactly the radial cutoff energy.

Let M be the integral of the squared norm of the untruncated primitive W, and let E_n be the already proved total cutoff gradient energy. The cutoff has norm at most one, so its value norm squared is at most M. Each of its two angular component energies is nonnegative and at most the total angular energy. Consequently

```
norm(v_n)^2 <= M + 2 E_n.
```

The existing native cutoff-energy theorem proves that E_n converges to a finite original source pairing. It therefore has a finite upper bound. This gives one finite bound on all original form norms. No untruncated domain admission is used to obtain it.

## Exact value and strong convergence

The abstract Bochner/product isometry must retain the literal representative. Its agreement on pure tensors, followed by Fubini for the actual L² pairing, shows that it maps an angular-L²-valued radial function to the specified original-product L² field whenever their rows agree almost everywhere. Density of the separated tensor image identifies the entire L² vector.

Applied to the actual native angular family, this gives

```
jointEmbedding(v_n) = L2(eta_n W).
```

At almost every original modular point the complete cutoff germ is eventually one. The squared value error is bounded by `4 norm(W)^2`, whose integral is finite by the already proved native L² admission. Dominated convergence gives strong convergence of these original value projections to L2(W).

## Admission through the dense adjoint range

Let K be the original injective joint embedding. The orthogonal-complement identity gives

```
closure(range(K*)) = orthogonal(ker K) = the full form domain.
```

For each psi in the original spatial L² space,

```
inner(v_n,K* psi) = inner(K v_n,psi).
```

Strong convergence of the original values therefore gives convergence of every pairing against the dense range of K*. The existing `WeakLimitBoundedFamily.exists_weakLimit_of_bounded` upgrades these limits and the uniform form bound to a weak limit v inside the original Hilbert form domain. Uniqueness of the scalar pairing limits gives `K v=L2(W)`. This is the required native form-domain admission. It does not require separately constructing the untruncated derivative quotient classes first.

## Lean modules and audit

[ThetaCuspHawkingBMNativeFormBound.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeFormBound.lean) contains `nativeCuspJointGraph_norm_sq_bound` and `nativeCuspJointGraph_bounded`.

[ThetaCuspHawkingBMNativeFormAdmission.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeFormAdmission.lean) contains `nativeCuspJointGraph_value`, `nativeCuspJointGraph_value_tendsto`, and `nativeJointTimePrimitive_form_admission`.

Both complete candidates passed scratch checks with `lake env lean`. Exact-module final audits passed:

- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFormBound`: 187 source lines; three jobs; 139 seconds reported build time.
- `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeFormAdmission`: 182 source lines; four jobs; 73 seconds reported build time.

The builds reused cached imports in the isolated leaf environment, including the existing weak-limit module. No dependency or umbrella rebuild ran. Separate scratch axiom audits checked only the two new form-bound theorems and three new admission theorems. All use only `propext`, `Classical.choice`, and `Quot.sound`. Together with the seven smoothing theorems, twelve new public theorems were audited without repeating older axiom checks.

The final sources and their five emitted artifacts were installed byte for byte. All three new leaves are imported in `RHTower.lean`. Final lint and cleanup are recorded below. The frontier map remains untouched. No new route-independent RH constraint was inferred, so the universal-law ledger was not changed. No numerical experiment ran.

## Next mathematical target

Native form admission is closed. The remaining immediate target is the original operator equation. `jointCoreDifferential_inner` already represents the full completed energy form on every original separated smooth core field. Prove the native transposed elliptic identity against those same tests, retaining the literal source G and all original seam and radial relations. Density then identifies the admitted form vector with `K*(W+G)`, giving

```
W = K K* (W+G).
```

This is the bounded-resolvent identity needed for the complete native/physical causal inverse comparison. Admission alone does not prove this equation, the complete physical-current cancellation, fixed-clock extinction, or RH.

## Search evidence

Broad and deep corpus searches used own terms and mechanism descriptions: Friedrichs, Douglas factorization, graph approximation, weak-limit admission, uncurry and transposition. Candidate lemmas, source arguments, method descriptions and generated ingredient groups were inspected together with partial and compiler-freshness metadata. The decisive weak-limit ingredient was verified from its actual source and applied to the original embedding. Other proposed groups were not accepted as proofs. A follow-up operator search and source verification located `jointCoreDifferential_inner` for the next exact equation. The distant-field intertwining comparison is recorded in the smoothing report; no external paper theorem is a Lean premise.

## Final gate and cleanup

`scripts/formal_tools.py lint` passed, with large-file warnings elsewhere in the corpus. All 48 relative links in the six affected reports/cards resolve. Every owned Lean, Lake, lint and research process reached observed terminal status. The isolated scratch/audit directory and eight owned search-result files were removed; no owned Lean or Lake process remained. No umbrella build, Git command, launcher or numerical experiment was run. The frontier map and universal-law ledger remain untouched.
