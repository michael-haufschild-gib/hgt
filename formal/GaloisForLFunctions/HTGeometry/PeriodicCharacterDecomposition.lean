import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Periodic functions as sums of character convolutions

Let `Ψ : ℤ/N → ℂ`.  Every `n ≥ 1` factors uniquely as `n = m r` with `m` `N`-smooth (all prime
factors divide `N`) and `r` coprime to `N` (`exists_smooth_coprime_split`,
`smooth_coprime_split_unique`).  For `m` `N`-smooth put

`c_χ(m) = φ(N)^{−1} Σ_{b ∈ (ℤ/N)ˣ} χ(b⁻¹) Ψ(m b)`.

Orthogonality of characters gives `Ψ(m r) = Σ_χ c_χ(m) χ(r)` for `r` coprime to `N`
(`sum_charSection_mul`).  Hence, for every completely multiplicative `f`,

`Ψ(n) f(n) = Σ_χ ((c_χ·f)|_{N-smooth} ⋆ χ f)(n)`   (`periodic_twist_eq_sum_convolution`).
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ### The smooth-coprime split -/

/-- `m` is `N`-smooth and `r` is coprime to `N`, so `m` and `r` are coprime. -/
theorem coprime_of_smooth_of_coprime {m r : ℕ} (hm : m ∈ Nat.factoredNumbers N.primeFactors)
    (hr : r.Coprime N) : m.Coprime r := by
  rw [Nat.coprime_comm, Nat.Coprime]
  by_contra h
  obtain ⟨p, hp, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpm : p ∈ m.primeFactorsList :=
    (Nat.mem_primeFactorsList (Nat.ne_zero_of_mem_factoredNumbers hm)).mpr ⟨hp, hpd.2⟩
  have hpN : p ∈ N.primeFactors := (Nat.mem_factoredNumbers.mp hm).2 p hpm
  have hpN' : p ∣ N := Nat.dvd_of_mem_primeFactors hpN
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpd.1 hr) hpN'

/-- **Uniqueness of the split.** -/
theorem smooth_coprime_split_unique {m r m' r' : ℕ}
    (hm : m ∈ Nat.factoredNumbers N.primeFactors) (hr : r.Coprime N)
    (hm' : m' ∈ Nat.factoredNumbers N.primeFactors) (hr' : r'.Coprime N)
    (h : m * r = m' * r') : m = m' := by
  have h1 : m ∣ m' := (coprime_of_smooth_of_coprime hm hr').dvd_of_dvd_mul_right
    (h ▸ dvd_mul_right m r)
  have h2 : m' ∣ m := (coprime_of_smooth_of_coprime hm' hr).dvd_of_dvd_mul_right
    (h.symm ▸ dvd_mul_right m' r')
  exact Nat.dvd_antisymm h1 h2

/-- **Existence of the split.** -/
theorem exists_smooth_coprime_split [NeZero N] {n : ℕ} (hn : n ≠ 0) :
    ∃ m r : ℕ, m ∈ Nat.factoredNumbers N.primeFactors ∧ r.Coprime N ∧ m * r = n := by
  set l := n.primeFactorsList with hl
  refine ⟨(l.filter (· ∈ N.primeFactors)).prod, (l.filter (fun x => x ∉ N.primeFactors)).prod,
    Nat.prod_mem_factoredNumbers _ _, ?_, ?_⟩
  · rw [Nat.coprime_list_prod_left_iff]
    intro p hp
    have hpl : p ∈ l := List.mem_of_mem_filter hp
    have hpN : p ∉ N.primeFactors := by
      have := List.of_mem_filter hp
      simpa only [decide_eq_true_eq] using this
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hpl
    rw [Nat.Prime.coprime_iff_not_dvd hpp]
    intro hdvd
    exact hpN (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, NeZero.ne N⟩)
  · have := Multiset.prod_filter_mul_prod_filter_not (s := (l : Multiset ℕ))
      (fun x => x ∈ N.primeFactors)
    simp only [Multiset.filter_coe, Multiset.prod_coe] at this
    rw [this, hl, Nat.prod_primeFactorsList hn]

/-! ### Character sections -/

/-- The `χ`-component of `b ↦ Ψ(m b)` on the units. -/
def charSection [NeZero N] (Ψ : ZMod N → ℂ) (χ : DirichletCharacter ℂ N) (m : ℕ) : ℂ :=
  ((N.totient : ℂ))⁻¹ * ∑ b : (ZMod N)ˣ, χ ((b : ZMod N)⁻¹) * Ψ ((m : ZMod N) * b)

/-- **Orthogonality.**  `Σ_χ c_χ(m) χ(r) = Ψ(m r)` for `r` coprime to `N`. -/
theorem sum_charSection_mul [NeZero N] (Ψ : ZMod N → ℂ) (m : ℕ) {r : ℕ} (hr : r.Coprime N) :
    ∑ χ : DirichletCharacter ℂ N, charSection Ψ χ m * χ r = Ψ ((m : ZMod N) * r) := by
  have hru : IsUnit (r : ZMod N) := (ZMod.isUnit_iff_coprime r N).mpr hr
  have htot : (N.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr
    (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  unfold charSection
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hb : ∀ b : (ZMod N)ˣ, ∑ χ : DirichletCharacter ℂ N,
      ((N.totient : ℂ))⁻¹ * (χ ((b : ZMod N)⁻¹) * Ψ ((m : ZMod N) * b)) * χ r =
      ((N.totient : ℂ))⁻¹ * Ψ ((m : ZMod N) * b) *
        (if (b : ZMod N) = r then (N.totient : ℂ) else 0) := by
    intro b
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ b.isUnit (r : ZMod N), Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [Finset.sum_congr rfl fun b _ => hb b]
  rw [Finset.sum_eq_single hru.unit]
  · simp only [IsUnit.unit_spec, if_true]
    field_simp
  · intro b _ hb'
    have : (b : ZMod N) ≠ r := fun h => hb' (Units.ext (by rw [h, IsUnit.unit_spec]))
    rw [if_neg this, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The twisted convolution identity -/

/-- The `N`-smooth section of `c_χ`, twisted by `f`. -/
def smoothSection [NeZero N] (Ψ : ZMod N → ℂ) (χ : DirichletCharacter ℂ N) (f : ℕ →*₀ ℂ) (m : ℕ) : ℂ :=
  open Classical in
  if m ∈ Nat.factoredNumbers N.primeFactors then charSection Ψ χ m * f m else 0

/-- **The character decomposition of a twisted periodic function.**  For `n ≥ 1`,
`Ψ(n) f(n) = Σ_χ (s_χ ⋆ χ f)(n)` with `s_χ = (c_χ f)|_{N-smooth}`. -/
theorem periodic_twist_eq_sum_convolution [NeZero N] (Ψ : ZMod N → ℂ) (f : ℕ →*₀ ℂ) {n : ℕ}
    (hn : n ≠ 0) :
    Ψ (n : ZMod N) * f n = ∑ χ : DirichletCharacter ℂ N,
      LSeries.convolution (smoothSection Ψ χ f) (fun r => χ r * f r) n := by
  classical
  obtain ⟨m, r, hm, hr, hmr⟩ := exists_smooth_coprime_split (N := N) hn
  have hterm : ∀ χ : DirichletCharacter ℂ N,
      LSeries.convolution (smoothSection Ψ χ f) (fun r => χ r * f r) n =
        charSection Ψ χ m * f m * (χ r * f r) := by
    intro χ
    rw [LSeries.convolution_def]
    show ∑ p ∈ n.divisorsAntidiagonal, smoothSection Ψ χ f p.1 * (χ p.2 * f p.2) = _
    rw [Finset.sum_eq_single (m, r)]
    · simp only [smoothSection, if_pos hm]
    · intro p hp hne
      have hpn : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
      by_cases hp1 : p.1 ∈ Nat.factoredNumbers N.primeFactors
      · by_cases hp2 : p.2.Coprime N
        · exfalso
          have h1 : p.1 = m := smooth_coprime_split_unique hp1 hp2 hm hr (hpn.trans hmr.symm)
          have h2 : p.2 = r := by
            have hm0 : m ≠ 0 := Nat.ne_zero_of_mem_factoredNumbers hm
            apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0)
            calc m * p.2 = p.1 * p.2 := by rw [h1]
              _ = m * r := hpn.trans hmr.symm
          exact hne (Prod.ext h1 h2)
        · have hχ : χ p.2 = 0 :=
            MulChar.map_nonunit χ (fun h => hp2 ((ZMod.isUnit_iff_coprime p.2 N).mp h))
          rw [hχ, zero_mul, mul_zero]
      · simp only [smoothSection, if_neg hp1, zero_mul]
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨hmr, hn⟩) h
  rw [Finset.sum_congr rfl fun χ _ => hterm χ]
  have e : ∀ χ : DirichletCharacter ℂ N, charSection Ψ χ m * f m * (χ r * f r) =
      (charSection Ψ χ m * χ r) * (f m * f r) := fun χ => by ring
  rw [Finset.sum_congr rfl fun χ _ => e χ, ← Finset.sum_mul, sum_charSection_mul Ψ m hr,
    ← map_mul, hmr, ← hmr]
  push_cast
  rfl

end

end GaloisForLFunctions.HTGeometry
