import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameValueGroup
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameKummerCharacters

/-! An automorphism in the decomposition group preserves the values of its finite
orbits. At distinct extensions of a finite place, products along those orbits give
inertia-fixed integral elements that are small at one place and reduce to one at the other. -/

noncomputable section

open NumberField IsDedekindDomain Polynomial
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

theorem exists_pow_valuation_lt {K : Type} [Field K] [CharZero K]
    (A : ValuationSubring K) {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : K) < 1)
    {x y : K} (hx : IsAlgebraic ℤ x) (hy : IsAlgebraic ℤ y) (hy₀ : y ≠ 0)
    (hxv : A.valuation x < 1) :
    ∃ n : ℕ, 0 < n ∧ A.valuation x ^ n < A.valuation y := by
  have hyv : 0 < A.valuation y := by simpa [pos_iff_ne_zero] using hy₀
  rcases eq_or_ne x 0 with rfl | hx₀
  · exact ⟨1, Nat.one_pos, by simpa using hyv⟩
  let u := A.valuation (p : K)
  have hu₀ : 0 < u := by simpa [u, pos_iff_ne_zero] using (Fact.out : p.Prime).ne_zero
  obtain ⟨m, k, hm, ha⟩ := exists_pow_valuation_eq_zpow A hp hx₀ hx
  obtain ⟨n, l, hn, hb⟩ := exists_pow_valuation_eq_zpow A hp hy₀ hy
  have hk : 0 < k := (zpow_lt_zpow_iff_right_of_lt_one₀ hu₀ hp).mp (by
    rw [zpow_zero, ← ha]
    exact pow_lt_one₀ zero_le hxv hm)
  let r := l.natAbs + 1
  have hr : l < (r : ℤ) := by
    have hle : l ≤ (l.natAbs : ℤ) := Int.le_natAbs
    dsimp [r]
    omega
  have hbound : l < k * (r : ℤ) * (n : ℤ) := by
    calc
      l < (r : ℤ) := hr
      _ = 1 * (r : ℤ) := (one_mul _).symm
      _ ≤ k * (r : ℤ) := mul_le_mul_of_nonneg_right (by omega) (Int.natCast_nonneg _)
      _ = (k * (r : ℤ)) * 1 := (mul_one _).symm
      _ ≤ k * (r : ℤ) * (n : ℤ) := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Nat.pos_of_ne_zero hn) (mul_nonneg hk.le (Int.natCast_nonneg _))
  refine ⟨m * r, Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.succ_pos _), ?_⟩
  apply (pow_lt_pow_iff_left₀ zero_le zero_le hn).mp
  rw [pow_mul, ha, hb, ← zpow_natCast (u ^ k) r, ← zpow_natCast ((u ^ k) ^ (r : ℤ)) n,
    ← zpow_mul, ← zpow_mul]
  exact zpow_lt_zpow_right_of_lt_one₀ hu₀ hp (by simpa only [mul_assoc] using hbound)

end GlobalTheory.TameKummer

namespace GlobalTheory.InertiaLift

/-- The orbit of an integral element lies in the finite root set of its minimal polynomial. -/
theorem exists_pos_pow_apply_eq {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    (σ : G E Ω) (x : Ω) (hx : IsIntegral E x) : ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
  have hmem (j : ℕ) : (σ ^ j) x ∈ (minpoly E x).rootSet Ω := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hx, ?_⟩
    have h := aeval_algHom_apply ((σ ^ j : G E Ω) : Ω →ₐ[E] Ω) x (minpoly E x)
    rwa [minpoly.aeval, map_zero] at h
  letI : Finite ((minpoly E x).rootSet Ω) := ((minpoly E x).rootSet_finite Ω).to_subtype
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun j : ℕ => (⟨(σ ^ j) x, hmem j⟩ : (minpoly E x).rootSet Ω))
  have h : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val heq
  have hperiod {i j : ℕ} (hij : i < j) (heq : (σ ^ i) x = (σ ^ j) x) :
      ∃ k : ℕ, 0 < k ∧ (σ ^ k) x = x := by
    refine ⟨j - i, Nat.sub_pos_of_lt hij, (σ ^ i).injective ?_⟩
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hij.le, heq]
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hperiod hij h
  · exact hperiod hji h.symm

/-- A decomposition-group element acts isometrically because any strict change
of value would produce a strictly monotone sequence on a finite orbit. -/
theorem valuation_apply_eq_of_mem_Dec {E Ω : Type*} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (x : Ω) :
    A.valuation (σ x) = A.valuation x := by
  have hcomp {u v : Ω} (hv : v ≠ 0) :
      A.valuation u ≤ A.valuation v ↔ u / v ∈ A := by
    rw [← A.valuation_le_one_iff, map_div₀, div_le_one₀ (by simpa [pos_iff_ne_zero] using hv)]
  have hle (u v : Ω) : A.valuation (σ u) ≤ A.valuation (σ v) ↔ A.valuation u ≤ A.valuation v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [hcomp (show σ v ≠ 0 by simpa using hv), hcomp hv, ← map_div₀,
        apply_mem_iff_of_mem_Dec hσ]
  have hlt (u v : Ω) : A.valuation (σ u) < A.valuation (σ v) ↔ A.valuation u < A.valuation v := by
    rw [lt_iff_not_ge, lt_iff_not_ge, hle]
  have hx : IsIntegral E x := (IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isAlgebraic x |>.isIntegral
  obtain ⟨n, hn, hfix⟩ := exists_pos_pow_apply_eq σ x hx
  let w (j : ℕ) := A.valuation ((σ ^ j) x)
  have heq : w n = w 0 := by
    change A.valuation ((σ ^ n) x) = A.valuation ((σ ^ 0) x)
    rw [hfix, pow_zero, AlgEquiv.one_apply]
  have hstep (j : ℕ) : w (j + 1) = A.valuation (σ ((σ ^ j) x)) := by
    change A.valuation ((σ ^ (j + 1)) x) = _
    rw [pow_succ', AlgEquiv.mul_apply]
  rcases lt_trichotomy (A.valuation (σ x)) (A.valuation x) with h | h | h
  · have hanti : StrictAnti w := strictAnti_nat_of_succ_lt (fun j => by
      induction j with
      | zero => simpa [w] using h
      | succ j ih =>
        rw [hstep (j + 1), hstep j]
        exact (hlt _ _).mpr ih)
    exact ((hanti hn).ne heq).elim
  · exact h
  · have hmono : StrictMono w := strictMono_nat_of_lt_succ (fun j => by
      induction j with
      | zero => simpa [w] using h
      | succ j ih =>
        rw [hstep j, hstep (j + 1)]
        exact (hlt _ _).mpr ih)
    exact ((hmono hn).ne heq.symm).elim

private theorem exists_integral_separating_places {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A B : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver A v) (hB : IsPlaceOver B v)
    (hAB : A ≠ B) {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    {c : Ω} (hc : IsIntegral ℤ c) (hc₀ : c ≠ 0) :
    ∃ e : Ω, IsIntegral ℤ e ∧ A.valuation e < A.valuation c ∧ B.valuation (1 - e) < 1 := by
  letI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  let I := primeBelow (F := E) A
  let J := primeBelow (F := E) B
  letI : I.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 E) I
    (by change (I.under (𝓞 E)).IsMaximal; rw [under_primeBelow hA]; exact v.isMaximal)
  letI : J.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 E) J
    (by change (J.under (𝓞 E)).IsMaximal; rw [under_primeBelow hB]; exact v.isMaximal)
  have hIJ : I ≠ J := by
    intro h
    apply hAB
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    let a : IntCl E Ω := ⟨b, hb.tower_top⟩
    have he := congrArg (fun P : Ideal (IntCl E Ω) => a ∈ P) h
    simpa only [I, J, mem_primeBelow, eq_iff_iff] using he
  have hle : ¬ I ≤ J := fun h => hIJ (Ideal.IsMaximal.eq_of_le inferInstance (Ideal.IsMaximal.ne_top ‹J.IsMaximal›) h)
  obtain ⟨x, hxI, hxJ⟩ := SetLike.not_le_iff_exists.mp hle
  have hxA : A.valuation (x : Ω) < 1 := (mem_primeBelow (F := E)).mp hxI
  obtain ⟨k, -, hk⟩ := GlobalTheory.TameKummer.exists_pow_valuation_lt A hp
    (isIntegral_int_of_isIntegral x.2).isAlgebraic hc.isAlgebraic hc₀ hxA
  have hxk : x ^ k ∉ J := fun h => hxJ (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  obtain ⟨y, i, hi, he⟩ := Ideal.IsMaximal.exists_inv ‹J.IsMaximal› hxk
  refine ⟨((y * x ^ k : IntCl E Ω) : Ω), isIntegral_int_of_isIntegral (y * x ^ k).2, ?_, ?_⟩
  · rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    exact (mul_le_of_le_one_left' (valuation_le_one_intCl A y)).trans_lt hk
  · have hi' : (1 : Ω) - ((y * x ^ k : IntCl E Ω) : Ω) = (i : Ω) := by
      have h := congrArg (fun z : IntCl E Ω => (z : Ω)) he
      simp only [AddMemClass.coe_add, OneMemClass.coe_one] at h
      rw [← h]
      ring
    rw [hi']
    exact (mem_primeBelow (F := E)).mp hi

private theorem valuation_le_one_of_one_sub_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x : Ω} (hx : A.valuation (1 - x) < 1) : A.valuation x ≤ 1 := by
  rw [show x = 1 - (1 - x) by ring]
  exact (Valuation.map_sub _ _ _).trans (max_le (by rw [map_one]) hx.le)

private theorem valuation_one_sub_mul_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    {x y : Ω} (hx : A.valuation (1 - x) < 1) (hy : A.valuation (1 - y) < 1) :
    A.valuation (1 - x * y) < 1 := by
  rw [show 1 - x * y = (1 - x) + x * (1 - y) by ring]
  refine Valuation.map_add_lt _ hx ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left' (valuation_le_one_of_one_sub_lt A hx)).trans_lt hy

/-- An integral separator can be chosen fixed by a prescribed inertia element
at the place where the separator reduces to one. -/
theorem exists_inertia_fixed_integral_separator {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A B : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hA : IsPlaceOver A v) (hB : IsPlaceOver B v)
    (hAB : A ≠ B) {p : ℕ} [Fact p.Prime] (hp : A.valuation (p : Ω) < 1)
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) {c : Ω} (hc : IsIntegral ℤ c) (hc₀ : c ≠ 0) :
    ∃ e : Ω, IsIntegral ℤ e ∧ σ e = e ∧ A.valuation e < A.valuation c ∧
      B.valuation (1 - e) < 1 := by
  obtain ⟨x, hx, hxA, hxB⟩ := exists_integral_separating_places A B v hA hB hAB hp hc hc₀
  obtain ⟨n, hn, hfix⟩ := exists_pos_pow_apply_eq σ x hx.tower_top
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let f (i : ℕ) : Ω := (σ ^ i) x
  have hf (i : ℕ) : IsIntegral ℤ (f i) :=
    hx.map ((σ ^ i : G E Ω).toRingEquiv.toRingHom.toIntAlgHom)
  have hstep (i : ℕ) : σ (f i) = f (i + 1) := by
    simp only [f, pow_succ', AlgEquiv.mul_apply]
  have hcong (i : ℕ) : B.valuation (1 - f i) < 1 := by
    induction i with
    | zero => simpa [f] using hxB
    | succ i ih =>
      have hmove := hσ.2 (f i) (valuation_le_one_of_one_sub_lt B ih)
      rw [show 1 - f (i + 1) = (1 - f i) + -(σ (f i) - f i) by rw [← hstep]; ring]
      refine Valuation.map_add_lt _ ih ?_
      rwa [Valuation.map_neg]
  refine ⟨∏ i ∈ Finset.range (m + 1), f i, IsIntegral.prod _ (fun i _ => hf i), ?_, ?_, ?_⟩
  · rw [map_prod]
    simp only [hstep]
    rw [Finset.prod_range_succ (fun i => f (i + 1)), Finset.prod_range_succ' f]
    have he : f (m + 1) = f 0 := by simpa [f] using hfix
    rw [he]
  · rw [Finset.prod_range_succ']
    have hi : IsIntegral ℤ (∏ i ∈ Finset.range m, f (i + 1)) :=
      IsIntegral.prod _ (fun i _ => hf (i + 1))
    have hval := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A hi)
    rw [map_mul, show f 0 = x by simp [f]]
    exact (mul_le_of_le_one_left' hval).trans_lt hxA
  · refine Finset.prod_induction f (fun y => B.valuation (1 - y) < 1)
      (fun _ _ => valuation_one_sub_mul_lt B) ?_ (fun i _ => hcong i)
    simp

end GlobalTheory.InertiaLift
