import Mathlib
import GaloisForLFunctions.Core

/-!
# Radial affine torsor and the cross-prime flatness no-go

Two graded components of different weights carry a one-parameter family of cross-grade relation
lines, and the radial character group acts on that family freely and transitively: every member has
trivial stabilizer, so no radial-equivariant datum can select one.

For a profile of radial slopes indexed by primes, the radial gauge acts by `b_p ↦ b_p + c log p`.
The normalized differences `κ_pq = b_p/log p − b_q/log q` are complete gauge invariants: they
determine the orbit and nothing more.  In particular the cross-prime flat locus is a single full
orbit, and the Riemann slope profile `b_p(ρ) = (2 Re ρ − 1) log p` is flat for **every** `ρ`, on or
off the critical line.  Cross-prime curvature therefore cannot select the critical slope.
-/

namespace HTGeometry.ConstraintRelativity

open Real

/-! ## The two-grade radial torsor -/

section Torsor

variable {g h : ℝ}

/-- The cross-grade relation line of parameter `λ` inside a two-grade component. -/
noncomputable def gradeLine (lam : ℝ) : Submodule ℝ (ℝ × ℝ) :=
  Submodule.span ℝ {((1 : ℝ), lam)}

/-- The radial character action on a two-grade component. -/
noncomputable def radialAction (g h c : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ :=
  (LinearMap.fst ℝ ℝ ℝ |>.smulRight (g ^ c, (0 : ℝ)))
    + (LinearMap.snd ℝ ℝ ℝ |>.smulRight ((0 : ℝ), h ^ c))

@[simp]
theorem radialAction_apply (g h c : ℝ) (v : ℝ × ℝ) :
    radialAction g h c v = (g ^ c * v.1, h ^ c * v.2) := by
  simp only [radialAction, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, Prod.smul_mk, smul_eq_mul, Prod.mk_add_mk, mul_zero, add_zero,
    zero_add, mul_comm]

/-- **Card `(2)`.**  The radial action moves the relation line of parameter `λ` to the line of
parameter `λ (h/g)^c`. -/
theorem map_gradeLine (hg : 0 < g) (hh : 0 < h) (c lam : ℝ) :
    Submodule.map (radialAction g h c) (gradeLine lam) = gradeLine (lam * (h / g) ^ c) := by
  have hgc : (0 : ℝ) < g ^ c := Real.rpow_pos_of_pos hg c
  have hkey : radialAction g h c ((1 : ℝ), lam) = (g ^ c) • ((1 : ℝ), lam * (h / g) ^ c) := by
    rw [radialAction_apply]
    refine Prod.ext ?_ ?_
    · simp
    · show h ^ c * lam = g ^ c * (lam * (h / g) ^ c)
      rw [Real.div_rpow hh.le hg.le]
      field_simp
  rw [gradeLine, gradeLine, Submodule.map_span, Set.image_singleton, hkey,
    Submodule.span_singleton_smul_eq]
  exact (isUnit_iff_ne_zero.2 hgc.ne').unit.isUnit

/-- **Card `(2)`, transitivity.**  For distinct positive grades the radial parameter map is a
bijection of `ℝ` onto the positive parameters. -/
theorem exists_unique_radial_parameter (hg : 0 < g) (hh : 0 < h) (hgh : g ≠ h)
    {lam lam' : ℝ} (hlam : 0 < lam) (hlam' : 0 < lam') :
    ∃! c : ℝ, lam * (h / g) ^ c = lam' := by
  have hq : 0 < h / g := div_pos hh hg
  have hq1 : h / g ≠ 1 := by
    intro hcon
    exact hgh (by field_simp at hcon; linarith [hcon])
  have hlog : Real.log (h / g) ≠ 0 := by
    intro hcon
    apply hq1
    have hexp := Real.exp_log hq
    rw [hcon, Real.exp_zero] at hexp
    exact hexp.symm
  refine ⟨Real.log (lam' / lam) / Real.log (h / g), ?_, ?_⟩
  · show lam * (h / g) ^ (Real.log (lam' / lam) / Real.log (h / g)) = lam'
    have hexp : Real.log (h / g) * (Real.log (lam' / lam) / Real.log (h / g))
        = Real.log (lam' / lam) := by field_simp
    rw [Real.rpow_def_of_pos hq, hexp, Real.exp_log (div_pos hlam' hlam)]
    field_simp
  · intro c hc
    have hpow : (h / g) ^ c = lam' / lam := by
      field_simp at hc ⊢
      linarith [hc]
    have := congrArg Real.log hpow
    rw [Real.log_rpow hq] at this
    field_simp at this ⊢
    linarith [this]

/-- **Trivial stabilizer.**  Only the identity radial character fixes a relation line. -/
theorem radial_stabilizer_trivial (hg : 0 < g) (hh : 0 < h) (hgh : g ≠ h)
    {lam : ℝ} (hlam : 0 < lam) {c : ℝ} (hc : lam * (h / g) ^ c = lam) : c = 0 := by
  obtain ⟨d, _, huniq⟩ := exists_unique_radial_parameter hg hh hgh hlam hlam
  rw [huniq c hc, huniq 0 (by simp)]

end Torsor

/-! ## The cross-prime gauge invariant -/

section CrossPrime

variable {ι : Type*} (w : ι → ℝ)

/-- The radial gauge action on a slope profile: `b_p ↦ b_p + c log p`. -/
def slopeAction (c : ℝ) (b : ι → ℝ) : ι → ℝ := fun i => b i + c * w i

/-- The normalized cross-prime difference `κ_pq = b_p/log p − b_q/log q`. -/
noncomputable def crossCurvature (b : ι → ℝ) (i j : ι) : ℝ := b i / w i - b j / w j

/-- **Card `(5)`, invariance.**  The cross-prime curvature is gauge invariant. -/
theorem crossCurvature_slopeAction (hw : ∀ i, w i ≠ 0) (c : ℝ) (b : ι → ℝ) (i j : ι) :
    crossCurvature w (slopeAction w c b) i j = crossCurvature w b i j := by
  have hi := hw i
  have hj := hw j
  simp only [crossCurvature, slopeAction, add_div, mul_div_assoc, div_self hi, div_self hj,
    mul_one]
  ring

/-- **Card `(5)`, completeness.**  Two profiles with equal cross-prime curvatures lie in the same
radial orbit. -/
theorem exists_slopeAction_of_crossCurvature_eq (hw : ∀ i, w i ≠ 0) [Nonempty ι]
    {b b' : ι → ℝ} (hk : ∀ i j, crossCurvature w b i j = crossCurvature w b' i j) :
    ∃ c : ℝ, b' = slopeAction w c b := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨b' i₀ / w i₀ - b i₀ / w i₀, ?_⟩
  funext i
  have h := hk i i₀
  simp only [crossCurvature] at h
  simp only [slopeAction]
  have hwi := hw i
  have hkey : b' i / w i = b i / w i + (b' i₀ / w i₀ - b i₀ / w i₀) := by linarith [h]
  have hmul := congrArg (fun t : ℝ => t * w i) hkey
  simp only [add_mul, div_mul_cancel₀ _ hwi] at hmul
  exact hmul

/-- **Card `(6)`–`(7)`.**  A profile is cross-prime flat exactly when it is a radial multiple of
the weight, so the flat locus is one full orbit rather than a point. -/
theorem crossCurvature_eq_zero_iff (hw : ∀ i, w i ≠ 0) [Nonempty ι] (b : ι → ℝ) :
    (∀ i j, crossCurvature w b i j = 0) ↔ ∃ a : ℝ, ∀ i, b i = a * w i := by
  classical
  constructor
  · intro hflat
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine ⟨b i₀ / w i₀, fun i => ?_⟩
    have h := hflat i i₀
    simp only [crossCurvature, sub_eq_zero] at h
    have hwi := hw i
    have hmul := congrArg (fun t : ℝ => t * w i) h
    simp only [div_mul_cancel₀ _ hwi] at hmul
    rw [← hmul]
  · rintro ⟨a, ha⟩ i j
    simp only [crossCurvature, ha i, ha j]
    rw [mul_div_assoc, mul_div_assoc, div_self (hw i), div_self (hw j)]
    ring

/-- **Card `(8)`.**  The Riemann slope profile is cross-prime flat for **every** `ρ`, on or off the
critical line: cross-prime curvature cannot select the critical slope. -/
theorem riemannProfile_flat (hw : ∀ i, w i ≠ 0) (rho : ℂ) (i j : ι) :
    crossCurvature w (fun k => (2 * rho.re - 1) * w k) i j = 0 := by
  simp only [crossCurvature]
  rw [mul_div_assoc, mul_div_assoc, div_self (hw i), div_self (hw j)]
  ring

end CrossPrime

/-! ## The prime instance -/

/-- Prime logarithms are nonzero, so the general theory applies to the prime-indexed profile with
no extra hypothesis. -/
theorem log_prime_ne_zero {p : ℕ} (hp : p.Prime) : Real.log (p : ℝ) ≠ 0 := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  exact hpos.ne'

/-- The cross-prime curvature of the Riemann slope profile vanishes at every `ρ`. -/
theorem riemannProfile_prime_flat (P : Type*) (p : P → ℕ) (hp : ∀ i, (p i).Prime) (rho : ℂ)
    (i j : P) :
    crossCurvature (fun k => Real.log (p k : ℝ))
      (fun k => (2 * rho.re - 1) * Real.log (p k : ℝ)) i j = 0 :=
  riemannProfile_flat _ (fun k => log_prime_ne_zero (hp k)) rho i j

/-! ## Theorem 4: finite algebraic radial invariants are constant -/

section RadialInvariants

/-- The radial character of a frequency, as a monoid homomorphism from the additive flow. -/
noncomputable def expChar (lam : ℝ) : Multiplicative ℝ →* ℝ where
  toFun t := Real.exp (lam * Multiplicative.toAdd t)
  map_one' := by
    show Real.exp (lam * (0 : ℝ)) = 1
    rw [mul_zero, Real.exp_zero]
  map_mul' s t := by
    show Real.exp (lam * (Multiplicative.toAdd s + Multiplicative.toAdd t))
      = Real.exp (lam * Multiplicative.toAdd s) * Real.exp (lam * Multiplicative.toAdd t)
    rw [mul_add, Real.exp_add]

@[simp] theorem expChar_apply (lam t : ℝ) :
    expChar lam (Multiplicative.ofAdd t) = Real.exp (lam * t) := rfl

theorem expChar_injective : Function.Injective expChar := by
  intro lam mu h
  have h1 : Real.exp (lam * 1) = Real.exp (mu * 1) :=
    congrArg (fun f => f (Multiplicative.ofAdd (1 : ℝ))) h
  rw [mul_one, mul_one] at h1
  exact Real.exp_injective h1

/-- **Card `(10)`.**  Distinct radial frequencies give linearly independent characters. -/
theorem linearIndependent_expChar :
    LinearIndependent ℝ (fun lam : ℝ => ⇑(expChar lam)) :=
  (linearIndependent_monoidHom (Multiplicative ℝ) ℝ).comp expChar expChar_injective

/-- A finite combination of distinct radial frequencies that vanishes identically has zero
coefficients. -/
theorem coeff_eq_zero_of_expSum_eq_zero {ι : Type*} [Fintype ι] (lam : ι → ℝ)
    (hlam : Function.Injective lam) (a : ι → ℝ)
    (h : ∀ t : ℝ, ∑ i, a i * Real.exp (lam i * t) = 0) (i : ι) : a i = 0 := by
  classical
  have hind : LinearIndependent ℝ (fun i : ι => ⇑(expChar (lam i))) :=
    linearIndependent_expChar.comp lam hlam
  refine Fintype.linearIndependent_iff.1 hind a ?_ i
  funext t
  have ht := h (Multiplicative.toAdd t)
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, expChar] using ht

/-- **Theorem 4.**  A finite combination of *nonzero* radial frequencies that is constant along the
flow is identically zero: no nonconstant finite algebraic invariant survives the radial flow, so
every radial invariant of the prime torus is constant. -/
theorem expSum_const_iff {ι : Type*} [Fintype ι] (lam : ι → ℝ) (hlam : Function.Injective lam)
    (hne : ∀ i, lam i ≠ 0) (a : ι → ℝ) (c : ℝ)
    (h : ∀ t : ℝ, ∑ i, a i * Real.exp (lam i * t) = c) :
    (∀ i, a i = 0) ∧ c = 0 := by
  classical
  set lam' : Option ι → ℝ := fun o => o.elim 0 lam with hlam'
  set a' : Option ι → ℝ := fun o => o.elim (-c) a with ha'
  have hlam'inj : Function.Injective lam' := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd hij.symm (hne j)
    · exact absurd hij (hne i)
    · exact congrArg some (hlam hij)
  have hzero : ∀ t : ℝ, ∑ o : Option ι, a' o * Real.exp (lam' o * t) = 0 := by
    intro t
    rw [Fintype.sum_option]
    show (-c) * Real.exp (0 * t) + ∑ i, a i * Real.exp (lam i * t) = 0
    rw [zero_mul, Real.exp_zero, mul_one, h t]
    ring
  refine ⟨fun i => coeff_eq_zero_of_expSum_eq_zero lam' hlam'inj a' hzero (some i), ?_⟩
  have hc := coeff_eq_zero_of_expSum_eq_zero lam' hlam'inj a' hzero none
  show c = 0
  have : (-c) = 0 := hc
  linarith

/-- **Card `(9)`.**  The prime-frequency pairing is injective: distinct integer exponent vectors
give distinct radial frequencies.  This is what makes the exponents of a Laurent monomial visible
along the flow, and it rests on the `ℤ`-independence of prime logarithms. -/
theorem primeFrequency_injective {F : Type*} [Fintype F] (p : F → Nat.Primes)
    (hp : Function.Injective p) :
    Function.Injective (fun m : F → ℤ => ∑ i, (m i : ℝ) * Real.log ((p i : ℕ) : ℝ)) := by
  classical
  have hind : LinearIndependent ℤ (fun i : F => Real.log ((p i : ℕ) : ℝ)) :=
    (GaloisForLFunctions.logPrime_linearIndependent_int).comp p hp
  intro m m' hmm
  funext i
  have hmm' : ∑ j, (m j : ℝ) * Real.log ((p j : ℕ) : ℝ)
      = ∑ j, (m' j : ℝ) * Real.log ((p j : ℕ) : ℝ) := hmm
  have hdiff : ∑ j, (m j - m' j) • Real.log ((p j : ℕ) : ℝ) = 0 := by
    have hzs : ∀ j : F, (m j - m' j) • Real.log ((p j : ℕ) : ℝ)
        = (m j : ℝ) * Real.log ((p j : ℕ) : ℝ) - (m' j : ℝ) * Real.log ((p j : ℕ) : ℝ) := by
      intro j
      rw [zsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun j _ => hzs j), Finset.sum_sub_distrib, hmm', sub_self]
  have := Fintype.linearIndependent_iff.1 hind (fun j => m j - m' j) hdiff i
  omega

end RadialInvariants

/-! ## Theorem 5: a trace-one tensor does not frame individual legs -/

section LegFraming

/-- **Theorem 5, `(11)`.**  Pure factorizations of a fixed nonzero product form a `ℂˣ`-torsor: any
two differ by a unique nonzero scale, acting by `(x, y) ↦ (r x, r⁻¹ y)`. -/
theorem exists_unique_factorization_scale {c x y x' y' : ℂ} (hc : c ≠ 0)
    (h : x * y = c) (h' : x' * y' = c) :
    ∃! r : ℂ, x' = r * x ∧ y' = r⁻¹ * y := by
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_mul] at h
    exact hc h.symm
  have hx' : x' ≠ 0 := by
    intro hx0
    rw [hx0, zero_mul] at h'
    exact hc h'.symm
  refine ⟨x' / x, ⟨(div_mul_cancel₀ x' hx).symm, ?_⟩, ?_⟩
  · rw [inv_div]
    field_simp
    linear_combination h' - h
  · rintro r ⟨hr, _⟩
    rw [hr]
    field_simp

/-- **Theorem 5, `(12)`.**  Acting by the scale `r` moves the transverse line `ℂ(x + y)` to
`ℂ(x + r⁻² y)`: the tensor, the trace normalization and the reciprocal pairing are all fixed, the
transverse line is not. -/
theorem span_transverse_scale (x y : ℂ) {r : ℂ} (hr : r ≠ 0) :
    Submodule.span ℂ {((r * x, r⁻¹ * y) : ℂ × ℂ)}
      = Submodule.span ℂ {((x, (r * r)⁻¹ * y) : ℂ × ℂ)} := by
  have hsmul : ((r * x, r⁻¹ * y) : ℂ × ℂ) = r • ((x, (r * r)⁻¹ * y) : ℂ × ℂ) := by
    refine Prod.ext rfl ?_
    show r⁻¹ * y = r * ((r * r)⁻¹ * y)
    field_simp
  rw [hsmul]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 r hr) _

/-- **Theorem 5, the no-go.**  No transverse line in `L₊ ⊕ L₋` is natural from the tensor alone:
whenever the scale is not a square root of one, the moved line is a different line. -/
theorem span_transverse_ne {x y r : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hr2 : r * r ≠ 1) :
    Submodule.span ℂ {((x, y) : ℂ × ℂ)} ≠ Submodule.span ℂ {((x, (r * r)⁻¹ * y) : ℂ × ℂ)} := by
  intro hEq
  have hmem : ((x, (r * r)⁻¹ * y) : ℂ × ℂ) ∈ Submodule.span ℂ {((x, y) : ℂ × ℂ)} := by
    rw [hEq]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have h1 : a * x = x := congrArg Prod.fst ha
  have h2 : a * y = (r * r)⁻¹ * y := congrArg Prod.snd ha
  have ha1 : a = 1 := mul_right_cancel₀ hx (by rw [h1, one_mul])
  rw [ha1, one_mul] at h2
  have hrr : (r * r)⁻¹ = 1 := by
    refine mul_right_cancel₀ hy ?_
    rw [one_mul, ← h2]
  refine hr2 ?_
  have hinv := congrArg (fun z : ℂ => z⁻¹) hrr
  simpa using hinv

end LegFraming

end HTGeometry.ConstraintRelativity
