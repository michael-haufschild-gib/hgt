import GaloisForLFunctions.RHTower.WeilConeResonanceMoments

/-!
# The resonance budget of the Weil cone

Let `λ` be full-cone Weil-positive and `½ < σ₀ ≤ 3/4`. For every finite set `P` of primes,

`Σ_{C ⊆ P} λ(∏C) (∏C)^{−σ₀} 2^{−|C|} ≤ K₁ + K₂ log ∏_{p∈P} p`   (`resonance_budget`),

with `K₁, K₂` depending only on `λ` and `σ₀`. Here `∏C` runs over the squarefree products of
primes in `P` (the term `C = ∅` vanishes, as `λ` is read on `n ≥ 2`).

**Proof.** Expand the resonator: `W_P(t) = ∏_{p∈P} |1 + p^{it}|²` equals
`Σ_{C⊆P} Σ_{A⊆C} 2^{|P∖C|} (∏A / ∏(C∖A))^{it}`. The twisted first moments of `D` on
`Re s = σ₀` (`exists_norm_integral_lamSeriesCont_sub_le`) give the main term
`[∏(C∖A) ∣ ∏A] λ(∏A/∏(C∖A)) (·)^{−σ₀} T`. Disjoint prime sets divide only when `C∖A = ∅`, so
`∫ D W_P = T Σ_{C⊆P} 2^{|P∖C|} λ(∏C)(∏C)^{−σ₀} + O(Q^{O(1)} log T)`, with `Q = ∏_{p∈P} p`.
Herglotz positivity gives `Re D(σ₀ + it) ≤ K log(2T + 3) + 1` (`exists_re_lamSeriesCont_le`),
and `W_P ≥ 0` has mass `2^{|P|} T + O(Q³)`. Take `T = Q⁶ T₁`.

**Corollary** (`exists_squarefree_lt`). For every `c > 0` and `n₀` there is a squarefree `n > n₀`
with `λ(n) < c`. Indeed, `λ ≥ c` on the squarefree numbers above `n₀` would make the left side
at least `c(∏_{n₀<p≤y}(1 + 1/(2p^{3/4})) − 1) ≥ c(exp(y^{1/4}/C) − 1)`. That beats `K₂ θ(y)`.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation

namespace RHTower.WeilResonance

local notation "eχ" => _root_.GaloisForLFunctions.expChar

variable {lam : ℕ → ℝ}

/-! ## Expanding the resonator -/

/-- `∏_{p∈C} p` as a natural number. -/
abbrev nprod (C : Finset ℕ) : ℕ := ∏ p ∈ C, p

theorem nprod_pos {C : Finset ℕ} (hC : ∀ p ∈ C, p.Prime) : 1 ≤ nprod C :=
  Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp => (hC p hp).ne_zero)

theorem log_nprod {C : Finset ℕ} (hC : ∀ p ∈ C, p.Prime) :
    Real.log (nprod C : ℝ) = ∑ p ∈ C, Real.log p := by
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp; exact_mod_cast (hC p hp).ne_zero

theorem two_cos_eq_expChar (q t : ℝ) :
    ((2 * Real.cos (t * q) : ℝ) : ℂ) = eχ q t + eχ (-q) t := by
  have h := ZetaResonator.two_cos_mul_expChar q 0 t
  have h0 : eχ 0 t = 1 := by unfold _root_.GaloisForLFunctions.expChar; simp
  rw [h0, mul_one, zero_add, zero_sub] at h
  exact h

/-- **The resonator expansion** `W_P = Σ_{C⊆P} Σ_{A⊆C} 2^{|P∖C|} (∏A/∏(C∖A))^{it}`. -/
theorem resW_eq_sum {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (t : ℝ) :
    (ZetaResonator.resW P t : ℂ) = ∑ C ∈ P.powerset, ∑ A ∈ C.powerset,
      (2 : ℂ) ^ (P \ C).card * eχ (Real.log (nprod A) - Real.log (nprod (C \ A))) t := by
  classical
  unfold ZetaResonator.resW
  rw [Complex.ofReal_prod]
  have h1 : ∀ p ∈ P, (((2 + 2 * Real.cos (t * Real.log p)) : ℝ) : ℂ) =
      (eχ (Real.log p) t + eχ (-Real.log p) t) + 2 := by
    intro p _
    rw [Complex.ofReal_add, two_cos_eq_expChar, Complex.ofReal_ofNat]; ring
  rw [Finset.prod_congr rfl h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCP : C ⊆ P := Finset.mem_powerset.mp hC
  have hCp : ∀ p ∈ C, p.Prime := fun p hp => hP p (hCP hp)
  rw [Finset.prod_const, Finset.prod_add, Finset.sum_mul]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hAC : A ⊆ C := Finset.mem_powerset.mp hA
  have hAp : ∀ p ∈ A, p.Prime := fun p hp => hCp p (hAC hp)
  have hDp : ∀ p ∈ C \ A, p.Prime := fun p hp => hCp p (Finset.sdiff_subset hp)
  rw [_root_.GaloisForLFunctions.prod_expChar, _root_.GaloisForLFunctions.prod_expChar,
    _root_.GaloisForLFunctions.expChar_add, log_nprod hAp, log_nprod hDp, Finset.sum_neg_distrib,
    ← sub_eq_add_neg]
  ring

/-- Disjoint sets of primes: `∏(C∖A) ∣ ∏A` only if `C∖A = ∅`. -/
theorem sdiff_eq_empty_of_dvd {C A : Finset ℕ} (hC : ∀ p ∈ C, p.Prime) (hAC : A ⊆ C)
    (h : nprod (C \ A) ∣ nprod A) : C \ A = ∅ := by
  by_contra hne
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hpP : p.Prime := hC p (Finset.sdiff_subset hp)
  have hpd : p ∣ nprod (C \ A) := Finset.dvd_prod_of_mem _ hp
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpP.prime (fun q => q)).mp (hpd.trans h)
  have hqP : q.Prime := hC q (hAC hq)
  have : p = q := (Nat.prime_dvd_prime_iff_eq hpP hqP).mp hpq
  exact (Finset.mem_sdiff.mp hp).2 (this ▸ hq)

end RHTower.WeilResonance
