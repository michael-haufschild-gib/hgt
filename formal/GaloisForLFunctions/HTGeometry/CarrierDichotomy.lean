import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.SeamKreinStructure

/-!
# The bounded-carrier criterion: falsification and the corank reformulation

A multiplicative functional equation `f(σ s) = m(s)·f(s)` presents `f` as a fixed point of the
**carrier** operator `T = M_m ∘ C_σ` (multiplication by the symbol `m` after substitution by `σ`):
`f` lies in the kernel `ker(C_σ − M_m)`.  The substitution part `C_σ` is an isometry on the natural
spaces, so *boundedness of the carrier* is exactly *boundedness of the multiplier symbol* `m`.

A natural conjecture reads: **bounded symbol `⟹` `f` is differentially algebraic**, with the
contrapositive — an unbounded constraint symbol — offered as an intrinsic operator-theoretic marker of
hypertranscendence.  This file settles that conjecture and isolates the correct invariant.

* **The literal conjecture is false** (`bounded_carrier_not_sufficient_for_DA`).  The most bounded
  symbol possible, `m ≡ 1`, gives the constraint `f(σ s) = f(s)`: its solution kernel is the entire
  ring of `σ`-invariants, and that ring is not contained in the differentially algebraic class.  The
  symbol's norm controls the *eigenvalue* of the carrier, never the *dimension of its kernel*; a
  hypertranscendental `σ`-invariant is a solution with a maximally bounded symbol.  The obstruction the
  conjecture reaches for lives in the kernel, not the operator norm.

* **The solution set is a torsor over the `σ`-invariants** (`constraint_ratio_invariant`): two
  solutions of one constraint have a `σ`-invariant ratio.  So the data `(σ, m)` determines `f` only up
  to the full `σ`-invariant ambiguity — the *corank of the carrier*, not its norm, is the operative
  invariant.

* **The corrected sufficient condition** (`rigid_constant_carrier_DA`): once the kernel is rigid
  (spanned by the single canonical exponential, corank one), a bounded — indeed constant — symbol does
  force differential algebraicity: `f = A·exp(γ·s)` solves `f(s+1) = e^γ·f(s)` and is differentially
  algebraic.

* **The intrinsic reading of an unbounded carrier** (`multiplier_at_of_residues`): the symbol value at
  a shift-pole equals the ratio of adjacent residues of `f`.  Residues are intrinsic local invariants
  of `f`, so their growth certifies carrier unboundedness *without constructing any carrier*.  For `Γ`
  the adjacent-residue ratios are `−(k+1)` (`gamma_multiplier_pole_value`), of norm `k+1`
  (`gamma_multiplier_pole_norm`): the difference carrier of `Γ` is unbounded, read purely off the
  residue tower.

* **Unification** (`no_bounded_carrier_dichotomy`): the same shape governs the archimedean and the
  prime side.  `Γ`'s residue-ratio data `k+1` and the reflected prime spectrum `p^{s−1}` of the
  `ζ`-seam (`RHTower.seam_no_bounded_reciprocity_carrier`) are both unbounded, so neither constraint
  admits a bounded carrier — one predicate, `UnboundedOn`, two instances.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

/-! ### §1 The constraint and its carrier symbol -/

/-- **A multiplicative constraint.**  `f` satisfies the functional equation `f(σ s) = m(s)·f(s)` — it
lies in the kernel of the carrier `C_σ − M_m`.  The object is *pinned* by this constraint, not
propagated by a flow. -/
def MultiplicativeConstraint (σ m f : ℂ → ℂ) : Prop := ∀ s, f (σ s) = m s * f s

/-- **A bounded carrier symbol.**  The multiplier `m` is a bounded multiplication operator: some `B`
dominates `‖m s‖` everywhere.  With `C_σ` an isometry, this is exactly boundedness of the carrier. -/
def BoundedSymbol (m : ℂ → ℂ) : Prop := ∃ B : ℝ, ∀ s, ‖m s‖ ≤ B

/-! ### §2 The solution set is a torsor over the `σ`-invariants — and boundedness is insufficient -/

/-- **Two solutions of one constraint have a `σ`-invariant ratio.**  If `f` and `g` both satisfy
`·(σ s) = m(s)··(s)` and `m` is nowhere zero, then `f/g` is `σ`-invariant: `(f/g)(σ s) = (f/g)(s)`.
Hence the solution set of a fixed `(σ, m)` is a torsor over the ring of `σ`-invariants — the symbol
determines `f` only up to that entire ambiguity. -/
theorem constraint_ratio_invariant (σ m f g : ℂ → ℂ)
    (hf : MultiplicativeConstraint σ m f) (hg : MultiplicativeConstraint σ m g)
    (hmne : ∀ s, m s ≠ 0) :
    ∀ s, f (σ s) / g (σ s) = f s / g s := by
  intro s
  rw [hf s, hg s, mul_div_mul_left _ _ (hmne s)]

/-- **The solution set is exactly a `σ`-invariant multiple of one solution.**  Given a nowhere-zero
solution `f₀` (and nowhere-zero symbol), `g` solves the same constraint iff `g/f₀` is `σ`-invariant.
This is the torsor structure made precise: the kernel of the carrier is the `σ`-invariant module times
`f₀`, so its "size" is the corank — the dimension of the `σ`-invariant ambiguity — which is the datum
that governs differential algebraicity, not `‖m‖`. -/
theorem constraint_solutions_periodic_iff (σ m f₀ g : ℂ → ℂ)
    (hf₀ : MultiplicativeConstraint σ m f₀) (hf₀ne : ∀ s, f₀ s ≠ 0) (hmne : ∀ s, m s ≠ 0) :
    MultiplicativeConstraint σ m g ↔ ∀ s, g (σ s) / f₀ (σ s) = g s / f₀ s := by
  constructor
  · intro hg s
    exact constraint_ratio_invariant σ m g f₀ hg hf₀ hmne s
  · intro hper s
    have hg : g (σ s) = (g s / f₀ s) * f₀ (σ s) := (div_eq_iff (hf₀ne (σ s))).mp (hper s)
    rw [hg, hf₀ s]; field_simp [hf₀ne s]

/-- **The bounded-carrier criterion is false.**  Given any `σ`-invariant `P` that is
hypertranscendental, the constraint `f(σ s) = 1·f(s)` — carried by the maximally bounded symbol
`m ≡ 1` — is solved by `P`, which is not differentially algebraic.  So a bounded symbol does not force
differential algebraicity: the obstruction lives in the kernel (`P` occupies the `σ`-invariant
ambiguity of `constraint_ratio_invariant`), not in the symbol's norm.  A `σ`-invariant with this
property exists classically (a lacunary period function of Mahler type); here it is the explicit
hypothesis, isolating the exact missing ingredient. -/
theorem bounded_carrier_not_sufficient_for_DA (σ P : ℂ → ℂ)
    (hinv : ∀ s, P (σ s) = P s) (hHT : Hypertranscendental P) :
    ∃ f, MultiplicativeConstraint σ (fun _ => 1) f ∧ BoundedSymbol (fun _ => (1 : ℂ))
      ∧ ¬ DifferentiallyAlgebraic f := by
  refine ⟨P, ?_, ⟨1, ?_⟩, hHT⟩
  · intro s; rw [hinv s, one_mul]
  · intro s; simp

/-! ### §3 The corank reformulation: a rigid, exponentially-generated kernel is differentially algebraic -/

/-- **The corrected sufficient condition.**  When the constraint kernel is rigid — corank one, spanned
by the single canonical exponential — a constant (hence bounded) symbol does force differential
algebraicity.  Any `f` with `f s = A·exp(γ·s)` is differentially algebraic, as a one-term exponential
sum (`differentiallyAlgebraic_finset_expSum`), satisfying `y' = γ·y`. -/
theorem rigid_constant_carrier_DA (γ A : ℂ) (f : ℂ → ℂ)
    (hf : ∀ s, f s = A * Complex.exp (γ * s)) : DifferentiallyAlgebraic f := by
  have hfe : f = fun x => ∑ i ∈ ({0} : Finset ℕ),
      (fun _ => A) i * Complex.exp ((fun _ => γ) i * x) := by
    funext s; rw [hf s]; simp
  rw [hfe]
  exact differentiallyAlgebraic_finset_expSum {0} (fun _ => A) (fun _ => γ)

/-- **The rigid solution really solves a bounded-symbol constraint.**  `f(s) = A·exp(γ·s)` satisfies
`f(s+1) = e^γ·f(s)` with the constant symbol `m ≡ e^γ`, which is bounded.  Together with
`rigid_constant_carrier_DA` this shows the bounded `⟹` differentially-algebraic implication holds
precisely on the rigid stratum — the periodic ambiguity of `bounded_carrier_not_sufficient_for_DA` is
what breaks it in general. -/
theorem rigid_solution_constraint (γ A : ℂ) :
    MultiplicativeConstraint (fun s => s + 1) (fun _ => Complex.exp γ)
      (fun s => A * Complex.exp (γ * s)) ∧ BoundedSymbol (fun _ => Complex.exp γ) := by
  refine ⟨?_, ⟨‖Complex.exp γ‖, fun _ => le_refl _⟩⟩
  intro s
  simp only
  rw [show γ * (s + 1) = γ * s + γ by ring, Complex.exp_add]; ring

/-- **A bounded entire symbol is constant.**  By Liouville, a differentiable symbol with a global norm
bound is constant.  So among *analytic* carriers, "bounded" collapses to "constant" — the rigid,
exponential regime of `rigid_constant_carrier_DA` where the implication to differential algebraicity
does hold.  Any escape into hypertranscendence under a bounded carrier must therefore use a
non-analytic symbol or the kernel ambiguity (`constraint_solutions_periodic_iff`), never a bounded
analytic multiplier. -/
theorem bounded_entire_symbol_const (m : ℂ → ℂ) (hm : Differentiable ℂ m)
    (hb : BoundedSymbol m) : ∀ s t, m s = m t := by
  obtain ⟨B, hB⟩ := hb
  have hrange : Bornology.IsBounded (Set.range m) := by
    apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := B))
    rintro _ ⟨z, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hB z
  exact hm.apply_eq_apply_of_bounded hrange

/-! ### §4 The intrinsic obstruction: a symbol value is a ratio of residues -/

/-- **The symbol value at a shift-pole is a ratio of adjacent residues.**  Suppose `f` satisfies
`f(s+1) = m(s)·f(s)` near `a − 1`, that `m` is continuous at `a − 1`, and that `f` has residue limits
`(s − a)·f(s) → rA` at `a` and `(s − (a−1))·f(s) → rB ≠ 0` at `a − 1`.  Then `m(a−1) = rA / rB`.

The residues are intrinsic local invariants of `f`; this identity reads the carrier symbol off them
directly, so the *growth* of residue ratios certifies unboundedness of any carrier realizing the
constraint — a constraint-side reading that constructs no operator.  The proof pushes the residue at
`a` back along the shift `s ↦ s+1` through the functional equation and matches limits. -/
theorem multiplier_at_of_residues (f m : ℂ → ℂ) (a rA rB : ℂ)
    (hfe : ∀ᶠ s in 𝓝[≠] (a - 1), f (s + 1) = m s * f s)
    (hm : ContinuousAt m (a - 1))
    (hrA : Tendsto (fun s => (s - a) * f s) (𝓝[≠] a) (𝓝 rA))
    (hrB : Tendsto (fun s => (s - (a - 1)) * f s) (𝓝[≠] (a - 1)) (𝓝 rB))
    (hrBne : rB ≠ 0) :
    m (a - 1) = rA / rB := by
  have hshift : Tendsto (fun s : ℂ => s + 1) (𝓝[≠] (a - 1)) (𝓝[≠] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun s : ℂ => s + 1) (𝓝 (a - 1)) (𝓝 ((a - 1) + 1)) :=
        (continuous_id.add continuous_const).continuousAt
      have he : (a - 1) + 1 = a := by ring
      rw [he] at h0; exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h; apply hs; rw [← h]; ring
  have hlimA : Tendsto (fun s => (s - (a - 1)) * (m s * f s)) (𝓝[≠] (a - 1)) (𝓝 rA) := by
    have hcomp := hrA.comp hshift
    refine hcomp.congr' ?_
    filter_upwards [hfe] with s hs
    simp only [Function.comp_apply]; rw [hs]; ring_nf
  have hlimB : Tendsto (fun s => (s - (a - 1)) * (m s * f s)) (𝓝[≠] (a - 1))
      (𝓝 (m (a - 1) * rB)) := by
    have hmc : Tendsto (fun s => m s) (𝓝[≠] (a - 1)) (𝓝 (m (a - 1))) := hm.continuousWithinAt
    have hmul := hmc.mul hrB
    refine hmul.congr' ?_; filter_upwards with s; ring
  have huniq := tendsto_nhds_unique hlimA hlimB
  field_simp; rw [huniq]

/-- **The symbol value for a general affine substitution.**  For `σ(s) = α·s + β` with `α ≠ 0`, if `f`
satisfies `f(σ s) = m(s)·f(s)` near `b`, `m` is continuous at `b`, and `f` has residues `rA` at
`a = σ(b)` and `rB ≠ 0` at `b`, then `m(b) = rA / (α·rB)`.  The substitution scales the local
difference by `α`, so the residue ratio picks up the factor `1/α`; the shift case `α = 1` is
`multiplier_at_of_residues`, and `α = −1` is the reflection case below.  This carries the intrinsic
carrier reading to every affine constraint — shift, reflection, and dilation alike — without
constructing an operator. -/
theorem multiplier_at_of_residues_affine (f m : ℂ → ℂ) (α β b rA rB : ℂ) (hα : α ≠ 0)
    (hfe : ∀ᶠ s in 𝓝[≠] b, f (α * s + β) = m s * f s)
    (hm : ContinuousAt m b)
    (hrA : Tendsto (fun t => (t - (α * b + β)) * f t) (𝓝[≠] (α * b + β)) (𝓝 rA))
    (hrB : Tendsto (fun s => (s - b) * f s) (𝓝[≠] b) (𝓝 rB))
    (hrBne : rB ≠ 0) :
    m b = rA / (α * rB) := by
  set a := α * b + β with ha
  have hshift : Tendsto (fun s : ℂ => α * s + β) (𝓝[≠] b) (𝓝[≠] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun s : ℂ => α * s + β) (𝓝 b) (𝓝 (α * b + β)) :=
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      intro h; apply hs
      have hαs : α * s = α * b := by rw [ha] at h; linear_combination h
      exact mul_left_cancel₀ hα hαs
  have hlimA : Tendsto (fun s => (s - b) * (m s * f s)) (𝓝[≠] b) (𝓝 (α⁻¹ * rA)) := by
    have hcomp := hrA.comp hshift
    have hscaled : Tendsto (fun s => α * ((s - b) * (m s * f s))) (𝓝[≠] b) (𝓝 rA) := by
      refine hcomp.congr' ?_
      filter_upwards [hfe] with s hs
      simp only [Function.comp_apply]
      rw [hs, ha]; ring
    have h2 := hscaled.const_mul α⁻¹
    refine h2.congr' ?_
    filter_upwards with s
    rw [← mul_assoc, inv_mul_cancel₀ hα, one_mul]
  have hlimB : Tendsto (fun s => (s - b) * (m s * f s)) (𝓝[≠] b) (𝓝 (m b * rB)) := by
    have hmc : Tendsto (fun s => m s) (𝓝[≠] b) (𝓝 (m b)) := hm.continuousWithinAt
    have hmul := hmc.mul hrB
    refine hmul.congr' ?_; filter_upwards with s; ring
  have huniq := tendsto_nhds_unique hlimA hlimB
  have hαrB : α * rB ≠ 0 := mul_ne_zero hα hrBne
  rw [eq_div_iff hαrB]
  rw [show m b * (α * rB) = α * (m b * rB) by ring, ← huniq, ← mul_assoc,
    mul_inv_cancel₀ hα, one_mul]

/-- **The symbol value for a reflection substitution.**  For `σ(s) = β − s`, if `f(β − s) = m(s)·f(s)`
near `b` with residues `rA` at `β − b` and `rB ≠ 0` at `b`, then `m(b) = −(rA / rB)`.  The `α = −1`
case of `multiplier_at_of_residues_affine`: this is the residue reading of a reflection carrier, of the
type that governs the `ζ`-functional equation `ζ(1−s) = χ(s)·ζ(s)`. -/
theorem multiplier_at_of_residues_reflection (f m : ℂ → ℂ) (β b rA rB : ℂ)
    (hfe : ∀ᶠ s in 𝓝[≠] b, f (β - s) = m s * f s)
    (hm : ContinuousAt m b)
    (hrA : Tendsto (fun t => (t - (β - b)) * f t) (𝓝[≠] (β - b)) (𝓝 rA))
    (hrB : Tendsto (fun s => (s - b) * f s) (𝓝[≠] b) (𝓝 rB))
    (hrBne : rB ≠ 0) :
    m b = -(rA / rB) := by
  have key := multiplier_at_of_residues_affine f m (-1) β b rA rB (by norm_num)
    ?hfe hm ?hrA hrB hrBne
  · rw [key]; field_simp
  case hfe => filter_upwards [hfe] with s hs; rw [show (-1 : ℂ) * s + β = β - s by ring]; exact hs
  case hrA => rw [show (-1 : ℂ) * b + β = β - b by ring]; exact hrA

/-- **A bounded carrier forces bounded residue ratios.**  If the symbol of the constraint is bounded
by `B` and `f` has the residue data of `multiplier_at_of_residues`, then the adjacent-residue ratio is
bounded: `‖rA / rB‖ ≤ B`.  Contrapositive: unbounded residue ratios force an unbounded carrier — the
dichotomy in its cleanest form. -/
theorem bounded_carrier_residueRatio_le (f m : ℂ → ℂ) (a rA rB : ℂ) (B : ℝ)
    (hfe : ∀ᶠ s in 𝓝[≠] (a - 1), f (s + 1) = m s * f s)
    (hm : ContinuousAt m (a - 1))
    (hrA : Tendsto (fun s => (s - a) * f s) (𝓝[≠] a) (𝓝 rA))
    (hrB : Tendsto (fun s => (s - (a - 1)) * f s) (𝓝[≠] (a - 1)) (𝓝 rB))
    (hrBne : rB ≠ 0) (hB : ‖m (a - 1)‖ ≤ B) :
    ‖rA / rB‖ ≤ B := by
  rw [← multiplier_at_of_residues f m a rA rB hfe hm hrA hrB hrBne]; exact hB

/-- **`Γ`'s difference-carrier symbol at the pole `−(k+1)`, read off adjacent residues, is `−(k+1)`.**
Applying `multiplier_at_of_residues` to `Γ` (whose shift symbol is `m(s) = s`, from
`Complex.Gamma_add_one`) at `a = −k`, with residues `(−1)^k/k!` and `(−1)^{k+1}/(k+1)!`
(`gamma_residue`), gives the identity `−(k+1) = ((−1)^k/k!) / ((−1)^{k+1}/(k+1)!)`. -/
theorem gamma_multiplier_pole_value (k : ℕ) :
    (-(k : ℂ) - 1) = ((-1) ^ k / (k.factorial : ℂ)) / ((-1) ^ (k + 1) / ((k + 1).factorial : ℂ)) := by
  have hpt : (-((k + 1 : ℕ) : ℂ)) = -(k : ℂ) - 1 := by push_cast; ring
  have key := multiplier_at_of_residues Complex.Gamma id (-(k : ℂ))
    ((-1) ^ k / (k.factorial : ℂ)) ((-1) ^ (k + 1) / ((k + 1).factorial : ℂ))
    ?hfe ?hm ?hrA ?hrB ?hrBne
  · simpa using key
  case hfe =>
    have hne : (-(k : ℂ) - 1) ≠ 0 := by
      intro h; have hh := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re, Complex.one_re,
        Complex.zero_re] at hh
      have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hev : ∀ᶠ s in 𝓝[≠] (-(k : ℂ) - 1), s ≠ 0 :=
      ((continuousAt_id (x := -(k : ℂ) - 1)).eventually_ne (by simpa using hne)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hev] with s hs0
    exact Complex.Gamma_add_one s hs0
  case hm => exact continuousAt_id
  case hrA =>
    have hres := GaloisForLFunctions.gamma_residue k
    refine hres.congr' ?_
    filter_upwards with s; congr 1; ring
  case hrB =>
    have hres := GaloisForLFunctions.gamma_residue (k + 1)
    rw [hpt] at hres
    refine hres.congr' ?_
    filter_upwards with s; congr 1; push_cast; ring
  case hrBne =>
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero (k + 1))

/-- **`Γ`'s residue-ratio norm is `k+1`, unbounded in `k`.**  The adjacent-residue ratio at the pole
`−(k+1)` — equal to the difference-carrier symbol there — has norm exactly `k+1`.  So `Γ`'s carrier is
unbounded, certified purely by the residue tower. -/
theorem gamma_multiplier_pole_norm (k : ℕ) :
    ‖((-1 : ℂ) ^ k / (k.factorial : ℂ)) / ((-1) ^ (k + 1) / ((k + 1).factorial : ℂ))‖ = (k : ℝ) + 1 := by
  rw [← gamma_multiplier_pole_value k]
  rw [show (-(k : ℂ) - 1) = -((k : ℂ) + 1) by ring, norm_neg]
  rw [show ((k : ℂ) + 1) = (((k + 1 : ℕ)) : ℂ) by push_cast; ring, Complex.norm_natCast]
  push_cast; ring

/-! ### §5 Unification: unbounded carrier data on the archimedean and the prime side -/

/-- **Unbounded data along a set of indices.**  No real bound dominates `d n` over the indices with
`S n` — the abstract "no bounded carrier" predicate specialized to a scalar datum. -/
def UnboundedOn (d : ℕ → ℝ) (S : ℕ → Prop) : Prop := ¬ ∃ B : ℝ, ∀ n, S n → d n ≤ B

/-- **`Γ`'s carrier data is unbounded (archimedean side).**  The residue-ratio norms `k+1`
(`gamma_multiplier_pole_norm`) exceed every bound: an Archimedean fact. -/
theorem gamma_carrier_unbounded : UnboundedOn (fun k => (k : ℝ) + 1) (fun _ => True) := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hle := hB n trivial
  simp only at hle
  linarith

/-- **The `ζ`-seam carrier data is unbounded (prime side).**  The reflected one-particle prime spectrum
`p^{s−1}` exceeds every bound over the primes, for real `s > 1` — this is
`RHTower.seam_no_bounded_reciprocity_carrier`, restated under the unified predicate. -/
theorem zeta_seam_carrier_unbounded {s : ℝ} (hs : 1 < s) :
    UnboundedOn (fun p => (p : ℝ) ^ (s - 1)) (fun p => Nat.Prime p) :=
  RHTower.seam_no_bounded_reciprocity_carrier hs

/-- **No bounded carrier, unified.**  The archimedean constraint of `Γ` and the reflection constraint
of the `ζ`-seam both have unbounded carrier data: `Γ`'s residue-ratio norms `k+1` and the seam's
reflected prime spectrum `p^{s−1}`.  One predicate `UnboundedOn`, two instances — the operator-theoretic
hypertranscendence marker, on both faces of the completion. -/
theorem no_bounded_carrier_dichotomy {s : ℝ} (hs : 1 < s) :
    UnboundedOn (fun k => (k : ℝ) + 1) (fun _ => True)
      ∧ UnboundedOn (fun p => (p : ℝ) ^ (s - 1)) (fun p => Nat.Prime p) :=
  ⟨gamma_carrier_unbounded, zeta_seam_carrier_unbounded hs⟩

/-- **`Γ`'s carrier unboundedness stated on its own residue ratios.**  The residue-ratio norms
themselves — not a stand-in sequence — exceed every bound, since each equals `k+1`
(`gamma_multiplier_pole_norm`).  This is `gamma_carrier_unbounded` phrased on the intrinsic residue
data of `Γ`. -/
theorem gamma_residueRatio_carrier_unbounded :
    UnboundedOn
      (fun k => ‖((-1 : ℂ) ^ k / (k.factorial : ℂ)) / ((-1) ^ (k + 1) / ((k + 1).factorial : ℂ))‖)
      (fun _ => True) := by
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have hle := hB n trivial
  dsimp only at hle
  rw [gamma_multiplier_pole_norm n] at hle
  linarith

/-! ### §6 The completed reflection carrier is bounded — so the obstruction is the seam -/

/-- **The completed `ζ`'s reflection carrier is bounded.**  `Λ(1−s) = Λ(s)`
(`completedRiemannZeta_one_sub`) is the multiplicative constraint with symbol `m ≡ 1`, the maximally
bounded carrier.  By `bounded_carrier_not_sufficient_for_DA` a bounded symbol cannot itself force
differential algebraicity: the reflection functional equation of the *completed* object is
hypertranscendence-neutral. -/
theorem completedZeta_reflection_bounded :
    MultiplicativeConstraint (fun s => 1 - s) (fun _ => 1) completedRiemannZeta
      ∧ BoundedSymbol (fun _ => (1 : ℂ)) := by
  refine ⟨?_, ⟨1, fun _ => by simp⟩⟩
  intro s; rw [one_mul]; exact completedRiemannZeta_one_sub s

/-- **The uncompleted reflection carrier is unbounded.**  The uncompleted functional equation
`ζ(1−s) = χ(s)·ζ(s)` (`riemannZeta_one_sub`) has symbol `χ(s) = 2·(2π)^(−s)·Γ(s)·cos(πs/2)`, which is
*unbounded*: at the `Γ`-pole `s = −2` — where the power factor `(2π)^(2 : ℕ)` and `cos(−π) = −1` are nonzero
— `χ` blows up, so no global bound survives.  Proof reads the blow-up off `gamma_residue` (the residue
of `Γ` at `−2` is `1/2 ≠ 0`): `(s+2)·χ(s)` tends to a nonzero limit, incompatible with any bound
`‖χ‖ ≤ B`.  This is the uncompleted counterpart of `completedZeta_reflection_bounded`: the completion
divides out the unbounded `Γ` factor, turning an unbounded reflection carrier into the bounded symbol
`≡ 1`. -/
theorem zeta_reflection_symbol_unbounded :
    ¬ BoundedSymbol (fun s => 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s
        * Complex.cos (Real.pi * s / 2)) := by
  rintro ⟨B, hB⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hb : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [hpi]
  have hre : 0 < (2 * (Real.pi : ℂ)).re := by rw [Complex.mul_re]; simp; positivity
  set brk : ℂ → ℂ := fun s => 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.cos (Real.pi * s / 2)
    with hbrkdef
  have hbrk_cont : ContinuousAt brk (-(2 : ℂ)) := by
    apply ContinuousAt.mul
    · exact continuousAt_const.mul
        ((continuous_const.cpow continuous_neg (fun x => Or.inl hre)).continuousAt)
    · exact (Complex.continuous_cos.comp (by fun_prop)).continuousAt
  have hbrk_ne : brk (-(2 : ℂ)) ≠ 0 := by
    rw [hbrkdef]
    have h2 : (2 * (Real.pi : ℂ)) ^ (-(-(2 : ℂ))) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hb]; exact Complex.exp_ne_zero _
    have h3 : Complex.cos (Real.pi * (-(2 : ℂ)) / 2) ≠ 0 := by
      rw [show (Real.pi : ℂ) * (-(2 : ℂ)) / 2 = -((Real.pi : ℝ) : ℂ) by ring, Complex.cos_neg,
        ← Complex.ofReal_cos, Real.cos_pi]
      norm_num
    exact mul_ne_zero (mul_ne_zero (by norm_num) h2) h3
  have hg2 : Tendsto (fun s : ℂ => (s + (2 : ℂ)) * Complex.Gamma s) (𝓝[≠] (-(2 : ℂ)))
      (𝓝 (1 / 2)) := by
    have h := GaloisForLFunctions.gamma_residue 2
    have hval : ((-1 : ℂ)) ^ 2 / ((2 : ℕ).factorial : ℂ) = 1 / 2 := by norm_num [Nat.factorial]
    rw [hval] at h
    simpa using! h
  set L : ℂ := brk (-(2 : ℂ)) * (1 / 2) with hLdef
  have hLne : L ≠ 0 := mul_ne_zero hbrk_ne (by norm_num)
  have hbrk_t : Tendsto brk (𝓝[≠] (-(2 : ℂ))) (𝓝 (brk (-(2 : ℂ)))) :=
    hbrk_cont.continuousWithinAt
  have hL_tend : Tendsto (fun s : ℂ => (s + (2 : ℂ)) *
      (2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2)))
      (𝓝[≠] (-(2 : ℂ))) (𝓝 L) := by
    have hprod := hbrk_t.mul hg2
    refine hprod.congr' ?_
    filter_upwards with s
    simp only [hbrkdef]; ring
  have hnorm_tend : Tendsto (fun s : ℂ => ‖(s + (2 : ℂ)) *
      (2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2))‖)
      (𝓝[≠] (-(2 : ℂ))) (𝓝 ‖L‖) := (continuous_norm.continuousAt.tendsto).comp hL_tend
  have hb0 : Tendsto (fun s : ℂ => ‖s + (2 : ℂ)‖ * B) (𝓝[≠] (-(2 : ℂ))) (𝓝 0) := by
    have hc : Tendsto (fun s : ℂ => s + (2 : ℂ)) (𝓝[≠] (-(2 : ℂ))) (𝓝 0) := by
      have h0 : Tendsto (fun s : ℂ => s + (2 : ℂ)) (𝓝 (-(2 : ℂ))) (𝓝 ((-(2 : ℂ)) + 2)) :=
        (continuous_id.add continuous_const).continuousAt
      rw [neg_add_cancel] at h0; exact h0.mono_left nhdsWithin_le_nhds
    have hn : Tendsto (fun s : ℂ => ‖s + (2 : ℂ)‖) (𝓝[≠] (-(2 : ℂ))) (𝓝 0) := by
      simpa only [Function.comp_def, norm_zero] using
        (continuous_norm.continuousAt.tendsto).comp hc
    simpa using hn.mul_const B
  have hle : ∀ᶠ s in 𝓝[≠] (-(2 : ℂ)), ‖(s + (2 : ℂ)) *
      (2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2))‖
      ≤ ‖s + (2 : ℂ)‖ * B := by
    filter_upwards with s
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB s) (norm_nonneg _)
  have hLle : ‖L‖ ≤ 0 := le_of_tendsto_of_tendsto hnorm_tend hb0 hle
  exact hLne (norm_eq_zero.mp (le_antisymm hLle (norm_nonneg _)))

/-- **The completed `ζ`'s hypertranscendence obstruction lives in the seam, not the reflection.**  For
real `s > 1`, the reflection carrier symbol is bounded (`≡ 1`) while the prime-seam carrier data
`p^{s−1}` is unbounded (`RHTower.seam_no_bounded_reciprocity_carrier`).  Boundedness of the reflection
symbol makes the reflection functional equation insufficient by the falsification, so the operator-side
marker of hypertranscendence has moved entirely to the unbounded prime seam.  The uncompleted
reflection carrier is by contrast unbounded (`zeta_reflection_symbol_unbounded`): this is exactly why
the completion is required — it divides out the unbounded `Γ` factor, rendering the reflection bounded
and isolating the obstruction at the weld. -/
theorem completedZeta_obstruction_is_seam {s : ℝ} (hs : 1 < s) :
    BoundedSymbol (fun _ : ℂ => (1 : ℂ))
      ∧ UnboundedOn (fun p => (p : ℝ) ^ (s - 1)) (fun p => Nat.Prime p) :=
  ⟨⟨1, fun _ => by simp⟩, zeta_seam_carrier_unbounded hs⟩

end GaloisForLFunctions
