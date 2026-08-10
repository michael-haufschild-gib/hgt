import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessDirichlet
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessSupport

/-!
# Kummer grading of a ramification power event

An integer is an `r`-th power exactly when every prime valuation is divisible by `r`, that is
exactly when its Kummer residue vector in `Λ/rΛ` vanishes.  The inherited power image is therefore
the trivial Kummer sector of the marked shell and the strict excess is the sum of all nontrivial
sectors.

On a finite aperture the Kummer quotient is a finite abelian group `G`; averaging a sector profile
against the dual group extracts the trivial coefficient, and Parseval turns the excess into the
`ℓ²` energy of the nontrivial sectors.  The two are comparable in both directions with the explicit
aperture factor `√(|G| - 1)`.

Composite ramification stages are glued by the exact sequence
`0 → ℤ/r →^{×s} ℤ/(sr) → ℤ/s → 0`, whose class in `H²(ℤ/s; ℤ/r) ≅ (ℤ/r)/s(ℤ/r)` is the carry
cocycle; it vanishes exactly for coprime stages.  On supports and on Dirichlet series the same
composition is flat: `C_{m,sr}(z) = C_{m,r}(sz) + C_{rm,s}(z)`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower Finset

/-! ## The Kummer residue of an integer -/

/-- **An integer is an `r`-th power exactly when `r` divides every prime valuation.** -/
theorem isRPow_iff_factorization_dvd {r N : ℕ} (hN : N ≠ 0) :
    IsRPow r N ↔ ∀ p : ℕ, r ∣ N.factorization p := by
  constructor
  · rintro ⟨k, rfl⟩ p
    rw [Nat.factorization_pow]
    exact ⟨k.factorization p, by simp⟩
  · intro hdvd
    refine ⟨∏ p ∈ N.primeFactors, p ^ (N.factorization p / r), ?_⟩
    rw [← Finset.prod_pow]
    have hterm : ∀ p ∈ N.primeFactors, (p ^ (N.factorization p / r)) ^ r
        = p ^ N.factorization p := by
      intro p _
      rw [← pow_mul, Nat.div_mul_cancel (hdvd p)]
    rw [Finset.prod_congr rfl hterm]
    exact (Nat.prod_primeFactors_pow_factorization hN).symm

/-- The Kummer residue vector of an integer in `Λ/rΛ`, coordinate at the prime `p`. -/
def kummerResidue (r N p : ℕ) : ZMod r := (N.factorization p : ZMod r)

/-- **The trivial Kummer sector is exactly the set of `r`-th powers.** -/
theorem isRPow_iff_kummerResidue_zero {r N : ℕ} (hN : N ≠ 0) :
    IsRPow r N ↔ ∀ p : ℕ, kummerResidue r N p = 0 := by
  rw [isRPow_iff_factorization_dvd hN]
  exact forall_congr' fun p => (ZMod.natCast_eq_zero_iff _ r).symm

open scoped Classical in
/-- **The Kummer grading of the marked shell.**  The inherited stream is the shell restricted to
the trivial residue sector; the excess stream is its complement. -/
theorem powerImageStream_eq_trivialSector (m r : ℕ) {N : ℕ} (hN : N ≠ 0) :
    powerImageStream m r N
      = if ∀ p : ℕ, kummerResidue r N p = 0 then shellIndicator (r * m) N else 0 := by
  rw [powerImageStream]
  by_cases h : ∀ p : ℕ, kummerResidue r N p = 0
  · rw [if_pos ((isRPow_iff_kummerResidue_zero hN).mpr h), if_pos h]
  · rw [if_neg (fun hx => h ((isRPow_iff_kummerResidue_zero hN).mp hx)), if_neg h]

open scoped Classical in
theorem excessStream_eq_nontrivialSector (m r : ℕ) {N : ℕ} (hN : N ≠ 0) :
    excessStream m r N
      = if ∀ p : ℕ, kummerResidue r N p = 0 then 0 else shellIndicator (r * m) N := by
  rw [excessStream]
  by_cases h : ∀ p : ℕ, kummerResidue r N p = 0
  · rw [if_pos ((isRPow_iff_kummerResidue_zero hN).mpr h), if_pos h]
  · rw [if_neg (fun hx => h ((isRPow_iff_kummerResidue_zero hN).mp hx)), if_neg h]

/-! ## Haar extraction and Parseval on a finite aperture -/

section Aperture

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The Kummer-phase transform of a sector profile: `Φ(ψ) = ∑_α A_α ψ(α)`. -/
noncomputable def sectorTransform (A : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ α : G, (A α : ℂ) * ψ α

/-- The normalised Haar average over the dual group. -/
noncomputable def haarAvg (f : AddChar G ℂ → ℂ) : ℂ :=
  ((Fintype.card G : ℂ))⁻¹ * ∑ ψ : AddChar G ℂ, f ψ

omit [DecidableEq G] in
theorem card_ne_zero_complex : ((Fintype.card G : ℂ)) ≠ 0 := by
  have : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  exact_mod_cast this

/-- Character orthogonality: the dual average of a character is the indicator of the trivial
class. -/
theorem haarAvg_char (α : G) :
    ((Fintype.card G : ℂ))⁻¹ * ∑ ψ : AddChar G ℂ, ψ α = if α = 0 then 1 else 0 := by
  rw [AddChar.sum_apply_eq_ite α]
  by_cases h : α = 0
  · rw [if_pos h, if_pos h, inv_mul_cancel₀ card_ne_zero_complex]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **Haar extraction of the inherited law.**  Averaging the Kummer-phase transform over the dual
group returns the trivial sector mass. -/
theorem haarAvg_sectorTransform (A : G → ℝ) :
    haarAvg (sectorTransform A) = (A 0 : ℂ) := by
  have hswap : ∑ ψ : AddChar G ℂ, sectorTransform A ψ
      = ∑ α : G, (A α : ℂ) * ∑ ψ : AddChar G ℂ, ψ α := by
    simp only [sectorTransform]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun α _ => (Finset.mul_sum _ _ _).symm
  rw [haarAvg, hswap, Finset.mul_sum]
  have hterm : ∀ α ∈ (Finset.univ : Finset G),
      ((Fintype.card G : ℂ))⁻¹ * ((A α : ℂ) * ∑ ψ : AddChar G ℂ, ψ α)
        = if α = 0 then (A α : ℂ) else 0 := by
    intro α _
    rw [← mul_assoc, mul_comm (((Fintype.card G : ℂ))⁻¹) ((A α : ℂ)), mul_assoc, haarAvg_char α]
    by_cases h : α = 0 <;> simp [h]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ (0 : G) (fun α => (A α : ℂ))]
  simp

/-- The centred Kummer-phase transform is the sum over nontrivial sectors. -/
theorem sectorTransform_sub (A : G → ℝ) (ψ : AddChar G ℂ) :
    sectorTransform A ψ - (A 0 : ℂ) = ∑ α ∈ Finset.univ.erase (0 : G), (A α : ℂ) * ψ α := by
  rw [sectorTransform, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : G))]
  simp

/-- **Kummer Parseval identity.**  The dual variance of the phase transform is the `ℓ²` energy of
the nontrivial sector masses. -/
theorem parseval_sectorTransform (A : G → ℝ) :
    ((Fintype.card G : ℝ))⁻¹ * ∑ ψ : AddChar G ℂ, ‖sectorTransform A ψ - (A 0 : ℂ)‖ ^ 2
      = ∑ α ∈ Finset.univ.erase (0 : G), (A α) ^ 2 := by
  have hnorm : ∀ ψ : AddChar G ℂ, ((‖sectorTransform A ψ - (A 0 : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = (sectorTransform A ψ - (A 0 : ℂ)) *
          (starRingEnd ℂ) (sectorTransform A ψ - (A 0 : ℂ)) := by
    intro ψ
    rw [Complex.mul_conj, ← Complex.normSq_eq_norm_sq]
  have hexpand : ∀ ψ : AddChar G ℂ,
      (sectorTransform A ψ - (A 0 : ℂ)) * (starRingEnd ℂ) (sectorTransform A ψ - (A 0 : ℂ))
        = ∑ α ∈ Finset.univ.erase (0 : G), ∑ β ∈ Finset.univ.erase (0 : G),
            (A α : ℂ) * (A β : ℂ) * ψ (α - β) := by
    intro ψ
    rw [sectorTransform_sub, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj, sub_eq_add_neg,
      AddChar.map_add_eq_mul]
    ring
  have hcomplex : ∑ ψ : AddChar G ℂ, ((‖sectorTransform A ψ - (A 0 : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = (Fintype.card G : ℂ) * ∑ α ∈ Finset.univ.erase (0 : G), ((A α : ℂ)) ^ 2 := by
    rw [Finset.sum_congr rfl fun ψ _ => (hnorm ψ).trans (hexpand ψ), Finset.sum_comm,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ β ∈ Finset.univ.erase (0 : G),
        ∑ ψ : AddChar G ℂ, (A α : ℂ) * (A β : ℂ) * ψ (α - β)
          = if β = α then (Fintype.card G : ℂ) * ((A α : ℂ)) ^ 2 else 0 := by
      intro β _
      rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite (α - β)]
      by_cases h : β = α
      · subst h
        rw [if_pos (sub_self β), if_pos rfl]
        ring
      · have hne : α - β ≠ 0 := fun hx => h (sub_eq_zero.mp hx).symm
        rw [if_neg hne, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hinner,
      Finset.sum_ite_eq' (Finset.univ.erase (0 : G)) α
        (fun _ => (Fintype.card G : ℂ) * ((A α : ℂ)) ^ 2), if_pos hα]
  have hreal : ((∑ ψ : AddChar G ℂ, ‖sectorTransform A ψ - (A 0 : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = ((Fintype.card G : ℝ) : ℂ) *
          ((∑ α ∈ Finset.univ.erase (0 : G), (A α) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, hcomplex, Complex.ofReal_sum]
    push_cast
    ring
  have hreal' : (∑ ψ : AddChar G ℂ, ‖sectorTransform A ψ - (A 0 : ℂ)‖ ^ 2 : ℝ)
      = (Fintype.card G : ℝ) * ∑ α ∈ Finset.univ.erase (0 : G), (A α) ^ 2 := by
    exact_mod_cast hreal
  rw [hreal', ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero (α := G))),
    one_mul]

/-! ## Two-sided comparison of excess and Kummer energy -/

/-- The analytic excess of a nonnegative sector profile. -/
noncomputable def sectorExcess (A : G → ℝ) : ℝ := ∑ α ∈ Finset.univ.erase (0 : G), A α

/-- The Kummer energy of a sector profile. -/
noncomputable def sectorEnergy (A : G → ℝ) : ℝ := ∑ α ∈ Finset.univ.erase (0 : G), (A α) ^ 2

/-- **The `ℓ² ≤ ℓ¹` half of the two-sided bound.** -/
theorem sqrt_sectorEnergy_le_sectorExcess {A : G → ℝ} (hA : ∀ α, 0 ≤ A α) :
    Real.sqrt (sectorEnergy A) ≤ sectorExcess A := by
  have hnn : 0 ≤ sectorExcess A := Finset.sum_nonneg fun α _ => hA α
  have hle : sectorEnergy A ≤ (sectorExcess A) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg fun α _ => hA α
  calc Real.sqrt (sectorEnergy A) ≤ Real.sqrt ((sectorExcess A) ^ 2) := Real.sqrt_le_sqrt hle
    _ = sectorExcess A := Real.sqrt_sq hnn

/-- **The Cauchy--Schwarz half of the two-sided bound.** -/
theorem sectorExcess_le_sqrt_card_mul {A : G → ℝ} (hA : ∀ α, 0 ≤ A α) :
    sectorExcess A
      ≤ Real.sqrt ((Fintype.card G : ℝ) - 1) * Real.sqrt (sectorEnergy A) := by
  have hpos : 1 ≤ Fintype.card G := Fintype.card_pos
  have hcard : ((Finset.univ.erase (0 : G)).card : ℝ) = (Fintype.card G : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp [Nat.cast_sub hpos]
  have hnn : 0 ≤ sectorExcess A := Finset.sum_nonneg fun α _ => hA α
  have hc : 0 ≤ (Fintype.card G : ℝ) - 1 := by
    rw [← hcard]; positivity
  have hsq : (sectorExcess A) ^ 2 ≤ ((Fintype.card G : ℝ) - 1) * sectorEnergy A := by
    rw [sectorExcess, sectorEnergy, ← hcard]
    exact sq_sum_le_card_mul_sum_sq
  have hstep := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hnn, Real.sqrt_mul hc] at hstep

end Aperture

/-- **Strict positivity of the Kummer energy.**  A single occupied nontrivial sector makes the
Parseval detector positive. -/
theorem sectorEnergy_pos {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {A : G → ℝ}
    {α : G} (hα : α ≠ 0) (hpos : 0 < A α) : 0 < sectorEnergy A := by
  refine Finset.sum_pos' (fun β _ => sq_nonneg _) ⟨α, Finset.mem_erase.mpr ⟨hα, Finset.mem_univ α⟩,
    pow_pos hpos 2⟩

/-! ## The Kummer carry extension of composite ramification stages -/

section Extension

variable (s r : ℕ)

/-- Multiplication by `s`: the kernel inclusion `ℤ/r → ℤ/(sr)` of a composite ramification
stage. -/
noncomputable def kummerIncl : ZMod r →+ ZMod (s * r) :=
  ZMod.lift r ⟨(zmultiplesHom (ZMod (s * r))) ((s : ℕ) : ZMod (s * r)), by
    simp only [zmultiplesHom_apply]
    rw [zsmul_eq_mul]
    push_cast
    rw [← Nat.cast_mul, mul_comm r s, ZMod.natCast_self]⟩

theorem kummerIncl_intCast (n : ℤ) :
    kummerIncl s r (n : ZMod r) = ((n * s : ℤ) : ZMod (s * r)) := by
  rw [kummerIncl, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, zsmul_eq_mul]
  push_cast
  ring

/-- Reduction modulo `s`: the quotient `ℤ/(sr) → ℤ/s`. -/
def kummerRed : ZMod (s * r) →+* ZMod s := ZMod.castHom ⟨r, rfl⟩ (ZMod s)

theorem kummerIncl_natCast (n : ℕ) :
    kummerIncl s r ((n : ℕ) : ZMod r) = ((n * s : ℕ) : ZMod (s * r)) := by
  have h := kummerIncl_intCast s r (n : ℤ)
  rw [show (((n : ℤ)) : ZMod r) = ((n : ℕ) : ZMod r) by push_cast; ring] at h
  rw [h]
  push_cast
  ring

theorem kummerRed_intCast (n : ℤ) : kummerRed s r ((n : ℤ) : ZMod (s * r)) = (n : ZMod s) :=
  map_intCast _ n

/-- The composite of the two stage maps vanishes. -/
theorem kummerRed_comp_kummerIncl (a : ZMod r) : kummerRed s r (kummerIncl s r a) = 0 := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
  rw [kummerIncl_intCast, kummerRed_intCast]
  push_cast
  rw [ZMod.natCast_self, mul_zero]

/-- **The stage inclusion is injective.** -/
theorem kummerIncl_injective (hs : s ≠ 0) : Function.Injective (kummerIncl s r) := by
  rw [kummerIncl, ZMod.lift_injective]
  intro n hn
  simp only [zmultiplesHom_apply, zsmul_eq_mul] at hn
  have hdvd : ((s * r : ℕ) : ℤ) ∣ n * s := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (n * s) (s * r)).mp (by push_cast at hn ⊢; simpa using hn)
    exact_mod_cast this
  have hs' : (0 : ℤ) < (s : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hs
  have hr : ((r : ℕ) : ℤ) ∣ n := by
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    have : (s : ℤ) * n = (s : ℤ) * ((r : ℤ) * k) := by push_cast at hk ⊢; linarith [hk]
    exact mul_left_cancel₀ (ne_of_gt hs') this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n r).mpr (by exact_mod_cast hr)

/-- **The stage quotient is surjective.** -/
theorem kummerRed_surjective : Function.Surjective (kummerRed s r) := by
  intro a
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
  exact ⟨((n : ℤ) : ZMod (s * r)), kummerRed_intCast s r n⟩

/-- **Exactness in the middle.**  The kernel of the stage quotient is the image of the stage
inclusion. -/
theorem kummerRed_eq_zero_iff (x : ZMod (s * r)) :
    kummerRed s r x = 0 ↔ ∃ a : ZMod r, kummerIncl s r a = x := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    rw [kummerRed_intCast] at hx
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd n s).mp hx
    refine ⟨((k : ℤ) : ZMod r), ?_⟩
    rw [kummerIncl_intCast]
    rw [hk]
    push_cast
    ring
  · rintro ⟨a, rfl⟩
    exact kummerRed_comp_kummerIncl s r a

/-! ### The carry cocycle -/

/-- The Kummer carry of the standard representatives. -/
def kummerCarry (a b : ZMod s) : ZMod r := (((a.val + b.val) / s : ℕ) : ZMod r)

theorem val_add_split {n : ℕ} [NeZero n] (a b : ZMod n) :
    a.val + b.val = n * ((a.val + b.val) / n) + (a + b).val := by
  rw [ZMod.val_add]
  exact (Nat.div_add_mod _ _).symm

/-- **The Kummer carry is a two-cocycle.** -/
theorem kummerCarry_cocycle [NeZero s] (a b c : ZMod s) :
    kummerCarry s r b c + kummerCarry s r a (b + c)
      = kummerCarry s r (a + b) c + kummerCarry s r a b := by
  have hs : s ≠ 0 := NeZero.ne s
  have h1 := val_add_split a b
  have h2 := val_add_split (a + b) c
  have h3 := val_add_split b c
  have h4 := val_add_split a (b + c)
  have hassoc : a + b + c = a + (b + c) := add_assoc a b c
  rw [hassoc] at h2
  have hnat : (b.val + c.val) / s + (a.val + (b + c).val) / s
      = (a.val + b.val) / s + ((a + b).val + c.val) / s := by
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hs) ?_
    rw [Nat.mul_add, Nat.mul_add]
    omega
  simp only [kummerCarry, ← Nat.cast_add, hnat]
  exact congrArg _ (Nat.add_comm _ _)

/-- **The carry is the extension defect of the standard section.** -/
theorem kummerCarry_extension_defect [NeZero s] (a b : ZMod s) :
    ((a.val : ℕ) : ZMod (s * r)) + ((b.val : ℕ) : ZMod (s * r))
        - (((a + b).val : ℕ) : ZMod (s * r))
      = kummerIncl s r (kummerCarry s r a b) := by
  have hsplit := val_add_split a b
  have hnat : a.val + b.val = ((a.val + b.val) / s) * s + (a + b).val := by
    conv_lhs => rw [hsplit]
    ring
  simp only [kummerCarry]
  rw [kummerIncl_natCast, ← Nat.cast_add]
  conv_lhs => rw [hnat]
  rw [Nat.cast_add]
  ring

/-- **Changing the set-theoretic section changes the carry by a coboundary**, so the extension
class is unaffected: a coboundary is itself a two-cocycle. -/
theorem coboundary_cocycle (t : ZMod s → ZMod r) (a b c : ZMod s) :
    (t b + t c - t (b + c)) + (t a + t (b + c) - t (a + (b + c)))
      = (t (a + b) + t c - t (a + b + c)) + (t a + t b - t (a + b)) := by
  rw [add_assoc a b c]
  ring

/-! ### The extension class vanishes exactly for coprime stages -/

/-- **The extension class is the class of `1` in `(ℤ/r)/s(ℤ/r)`**, so it vanishes exactly when
`s` is invertible modulo `r`. -/
theorem extension_class_zero_iff_coprime [NeZero r] :
    (∃ x : ZMod r, (s : ZMod r) * x = 1) ↔ Nat.Coprime s r := by
  rw [← ZMod.isUnit_iff_coprime s r]
  constructor
  · rintro ⟨x, hx⟩
    exact IsUnit.of_mul_eq_one x hx
  · rintro ⟨u, hu⟩
    exact ⟨(u⁻¹ : (ZMod r)ˣ), by rw [← hu]; exact u.mul_inv⟩

/-- **The composite stage splits exactly for coprime stages.** -/
theorem splits_iff_coprime (hs : s ≠ 0) (hr : r ≠ 0) :
    (∃ σ : ZMod s →+ ZMod (s * r), ∀ a : ZMod s, kummerRed s r (σ a) = a)
      ↔ Nat.Coprime s r := by
  haveI : NeZero s := ⟨hs⟩
  haveI : NeZero (s * r) := ⟨Nat.mul_ne_zero hs hr⟩
  constructor
  · rintro ⟨σ, hσ⟩
    set x : ZMod (s * r) := σ 1 with hx
    have hzero : (s : ℕ) • x = 0 := by
      rw [hx, ← map_nsmul]
      have : (s : ℕ) • (1 : ZMod s) = 0 := by
        rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]
      rw [this, map_zero]
    have hval : ((s * x.val : ℕ) : ZMod (s * r)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
      exact hzero

    have hdvd : (s * r) ∣ s * x.val := (ZMod.natCast_eq_zero_iff _ _).mp hval
    obtain ⟨k, hk⟩ := hdvd
    have hrk : x.val = r * k := by
      have hs' : 0 < s := Nat.pos_of_ne_zero hs
      have : s * x.val = s * (r * k) := by rw [hk]; ring
      exact Nat.eq_of_mul_eq_mul_left hs' this
    have hred : kummerRed s r x = 1 := hσ 1
    have hcast : kummerRed s r x = ((x.val : ℕ) : ZMod s) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      rw [map_natCast]
    rw [hcast, hrk] at hred
    have hunit : IsUnit ((r : ℕ) : ZMod s) := by
      refine IsUnit.of_mul_eq_one ((k : ℕ) : ZMod s) ?_
      rw [← Nat.cast_mul]
      exact hred
    have hcop : Nat.Coprime r s := (ZMod.isUnit_iff_coprime r s).mp hunit
    exact hcop.symm
  · intro hcop
    have hbezout : (1 : ℤ) = (s : ℤ) * Nat.gcdA s r + (r : ℤ) * Nat.gcdB s r := by
      have := Nat.gcd_eq_gcd_ab s r
      rw [hcop.gcd_eq_one] at this
      exact_mod_cast this
    set w : ZMod (s * r) := (((r : ℤ) * Nat.gcdB s r : ℤ) : ZMod (s * r)) with hw
    have hkill : ((s : ℤ)) • w = 0 := by
      rw [hw, zsmul_eq_mul]
      push_cast
      rw [show ((s : ZMod (s * r)) * ((r : ZMod (s * r)) *
            ((Nat.gcdB s r : ℤ) : ZMod (s * r))))
          = (((s * r : ℕ) : ZMod (s * r))) * ((Nat.gcdB s r : ℤ) : ZMod (s * r)) by
        push_cast; ring, ZMod.natCast_self, zero_mul]
    refine ⟨ZMod.lift s ⟨(zmultiplesHom (ZMod (s * r))) w, by
      simpa using hkill⟩, ?_⟩
    intro a
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    rw [ZMod.lift_coe]
    simp only [zmultiplesHom_apply, zsmul_eq_mul]
    rw [map_mul, hw, kummerRed_intCast, kummerRed_intCast]
    push_cast
    have hs0 : ((s : ℕ) : ZMod s) = 0 := ZMod.natCast_self s
    have hone : ((r : ℕ) : ZMod s) * ((Nat.gcdB s r : ℤ) : ZMod s) = 1 := by
      have := congrArg (fun z : ℤ => ((z : ℤ) : ZMod s)) hbezout
      push_cast at this
      rw [hs0] at this
      simpa using this.symm
    rw [hone, mul_one]

end Extension

/-! ## The analytic composition cocycle -/

/-- The excess Dirichlet series of a ramification power event. -/
noncomputable def excessLSeries (m r : ℕ) (z : ℂ) : ℂ :=
  LSeries (fun N => ((excessStream m r N : ℤ) : ℂ)) z

/-- The excess series is the difference between the deep shell and the dilated shallow shell. -/
theorem excessLSeries_eq_sub {m r : ℕ} (hr : r ≠ 0) {z : ℂ} (hz : 1 < z.re) :
    excessLSeries m r z
      = LSeries (fun N => ((shellIndicator (r * m) N : ℤ) : ℂ)) z
        - LSeries (fun k => ((shellIndicator m k : ℤ) : ℂ)) ((r : ℂ) * z) := by
  rw [excessLSeries, lSeries_shell_eq_dilate_add_excess hr hz]
  ring

/-- **The analytic Kummer composition cocycle.**  `C_{m,sr}(z) = C_{m,r}(sz) + C_{rm,s}(z)`. -/
theorem excessLSeries_cocycle {m r s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) {z : ℂ} (hz : 1 < z.re) :
    excessLSeries m (s * r) z
      = excessLSeries m r ((s : ℂ) * z) + excessLSeries (r * m) s z := by
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
  have hzre : 1 < ((s : ℂ) * z).re := by
    have hre : ((s : ℂ) * z).re = (s : ℝ) * z.re := by
      simp [Complex.mul_re]
    rw [hre]
    nlinarith [hz]
  have hsr : s * r ≠ 0 := Nat.mul_ne_zero hs hr
  rw [excessLSeries_eq_sub hsr hz, excessLSeries_eq_sub hr hzre, excessLSeries_eq_sub hs hz]
  have hshell : (s * r) * m = s * (r * m) := by ring
  have hdil : ((r : ℂ)) * ((s : ℂ) * z) = ((s * r : ℕ) : ℂ) * z := by
    push_cast; ring
  rw [hshell, hdil]
  ring

/-! ## The finite aperture and its arithmetic witness -/

/-- On a finite aperture of `d` primes the Kummer quotient has exactly `r^d` sectors. -/
theorem card_apertureKummer (F : Type*) [Fintype F] [DecidableEq F] (r : ℕ) [NeZero r] :
    Fintype.card (F → ZMod r) = r ^ Fintype.card F := by
  rw [Fintype.card_fun, ZMod.card r]

/-- **The excess witness has a nontrivial Kummer residue.**  The integer `2^{rm} · 3` lies in the
level-`rm` shell, is not an `r`-th power, and its residue at the prime `3` is the nonzero class
of `1`. -/
theorem excess_witness_kummerResidue {m r : ℕ} (hm : m ≠ 0) (hr : 2 ≤ r) :
    shellIndicator (r * m) (2 ^ (r * m) * 3) = 1
      ∧ ¬ IsRPow r (2 ^ (r * m) * 3)
      ∧ kummerResidue r (2 ^ (r * m) * 3) 3 ≠ 0 := by
  obtain ⟨hshell, hnot⟩ := excess_witness hm hr
  refine ⟨hshell, hnot, ?_⟩
  have hfac : (2 ^ (r * m) * 3 : ℕ).factorization 3 = 1 := by
    rw [factorization_two_pow_mul_three_apply]
    norm_num
  rw [kummerResidue, hfac, Nat.cast_one]
  haveI : Fact (1 < r) := ⟨by omega⟩
  exact one_ne_zero

/-! ## Capstone -/

/-- **The Kummer Parseval detector.**  On a finite aperture the analytic excess and the Kummer
phase variance determine one another up to the explicit aperture factor `√(r^d - 1)`, the Haar
average of the phase transform extracts the inherited image, and the detector is strictly positive
as soon as one nontrivial sector is occupied. -/
theorem kummer_parseval_detector {F : Type*} [Fintype F] [DecidableEq F] {r : ℕ} [NeZero r]
    {A : (F → ZMod r) → ℝ} (hA : ∀ α, 0 ≤ A α) {α₀ : F → ZMod r} (hα₀ : α₀ ≠ 0)
    (hpos : 0 < A α₀) :
    haarAvg (sectorTransform A) = (A 0 : ℂ)
      ∧ ((Fintype.card (F → ZMod r) : ℝ))⁻¹ *
          ∑ ψ : AddChar (F → ZMod r) ℂ, ‖sectorTransform A ψ - (A 0 : ℂ)‖ ^ 2
        = sectorEnergy A
      ∧ 0 < sectorEnergy A
      ∧ Real.sqrt (sectorEnergy A) ≤ sectorExcess A
      ∧ sectorExcess A
          ≤ Real.sqrt ((r : ℝ) ^ Fintype.card F - 1) * Real.sqrt (sectorEnergy A) := by
  refine ⟨haarAvg_sectorTransform A, parseval_sectorTransform A,
    sectorEnergy_pos hα₀ hpos, sqrt_sectorEnergy_le_sectorExcess hA, ?_⟩
  have hcard : ((Fintype.card (F → ZMod r) : ℝ)) = (r : ℝ) ^ Fintype.card F := by
    rw [card_apertureKummer F r]
    push_cast
    ring
  have := sectorExcess_le_sqrt_card_mul hA
  rwa [hcard] at this

/-- **The Kummer composition package.**  The support partition, the analytic cocycle, the exact
stage sequence, the carry two-cocycle, and the coprime splitting criterion. -/
theorem kummer_composition {m r s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0) [NeZero s] {z : ℂ}
    (hz : 1 < z.re) :
    excessSupport m (s * r) = excessSupport (r * m) s ∪ (fun k => k ^ s) '' excessSupport m r
      ∧ Disjoint (excessSupport (r * m) s) ((fun k => k ^ s) '' excessSupport m r)
      ∧ excessLSeries m (s * r) z
          = excessLSeries m r ((s : ℂ) * z) + excessLSeries (r * m) s z
      ∧ Function.Injective (kummerIncl s r)
      ∧ Function.Surjective (kummerRed s r)
      ∧ (∀ x : ZMod (s * r), kummerRed s r x = 0 ↔ ∃ a : ZMod r, kummerIncl s r a = x)
      ∧ (∀ a b c : ZMod s, kummerCarry s r b c + kummerCarry s r a (b + c)
          = kummerCarry s r (a + b) c + kummerCarry s r a b)
      ∧ ((∃ σ : ZMod s →+ ZMod (s * r), ∀ a : ZMod s, kummerRed s r (σ a) = a)
          ↔ Nat.Coprime s r) :=
  ⟨excessSupport_mul_eq_union hs, excessSupport_disjoint_image,
    excessLSeries_cocycle hr hs hz, kummerIncl_injective s r hs, kummerRed_surjective s r,
    kummerRed_eq_zero_iff s r, fun a b c => kummerCarry_cocycle s r a b c,
    splits_iff_coprime s r hs hr⟩

end HTGeometry.ConstraintFrameRelativity
