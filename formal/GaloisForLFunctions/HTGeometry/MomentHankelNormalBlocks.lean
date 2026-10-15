import GaloisForLFunctions.HTGeometry.MonicMomentAdmission

/-!
# Exact resolution of singular Hankel gaps

After a regular head of size `n`, let `P` be its canonical monic admission and
let `n+d-1` be the first row with `L(X^i P) ≠ 0`. For every `k ≤ d`, the
size-`n+k` kernel consists exactly of `P*q` with `degree q < min k (d-k)`.
Thus every intermediate head is singular, the next head is regular, and a
nondegenerate moment sequence has a unique normal block covering every rank.

The proof divides a kernel polynomial by `P`. Regularity kills the remainder;
the first nonzero moment coupling detects the quotient's highest coefficient.
No positivity, nonzero intermediate pivot, or generic parameter is assumed.
-/

open scoped BigOperators
open Polynomial Matrix

namespace HTGeometry
noncomputable section

/-- Polynomial kernel of a finite leading moment section. -/
def MomentSectionKernel (s : ℕ → ℝ) (N : ℕ) (p : ℝ[X]) : Prop :=
  p.degree < (N : WithBot ℕ) ∧
    ∀ i < N, momentFunctional s (X ^ i * p) = 0

/-- No nonzero polynomial is invisible to every moment row. -/
def NondegenerateMomentSequence (s : ℕ → ℝ) : Prop :=
  ∀ p : ℝ[X], (∀ i : ℕ, momentFunctional s (X ^ i * p) = 0) → p = 0

theorem momentFunctional_X_pow_mul_mul_eq_sum
    (s : ℕ → ℝ) (P q : ℝ[X]) (i : ℕ) :
    momentFunctional s (X ^ i * (P * q)) =
      ∑ k ∈ q.support, q.coeff k * momentFunctional s (X ^ (i + k) * P) := by
  have heq : X ^ i * (P * q) =
      ∑ k ∈ q.support, q.coeff k • (X ^ (i + k) * P) := by
    conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq q, Polynomial.sum_def]
    simp only [Finset.mul_sum, Polynomial.smul_eq_C_mul, pow_add]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq, momentFunctional_finset_sum]
  simp only [momentFunctional_smul]

theorem momentFunctional_X_pow_mul_mul_eq_zero
    {s : ℕ → ℝ} {P q : ℝ[X]} {i j : ℕ}
    (hz : ∀ k < j, momentFunctional s (X ^ k * P) = 0)
    (hq : ∀ k ∈ q.support, i + k < j) :
    momentFunctional s (X ^ i * (P * q)) = 0 := by
  rw [momentFunctional_X_pow_mul_mul_eq_sum]
  exact Finset.sum_eq_zero fun k hk => by rw [hz _ (hq k hk), mul_zero]

/-- At the first surviving moment row, only the leading coefficient survives. -/
theorem momentFunctional_X_pow_mul_mul_first
    {s : ℕ → ℝ} {P q : ℝ[X]} {i j : ℕ}
    (hz : ∀ k < j, momentFunctional s (X ^ k * P) = 0)
    (hij : i + q.natDegree = j) :
    momentFunctional s (X ^ i * (P * q)) =
      q.leadingCoeff * momentFunctional s (X ^ j * P) := by
  rw [momentFunctional_X_pow_mul_mul_eq_sum]
  rw [Finset.sum_eq_single q.natDegree]
  · rw [hij, Polynomial.coeff_natDegree]
  · intro k hk hkne
    have hkle := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hk)
    rw [hz _ (by omega), mul_zero]
  · intro hq
    have hc : q.coeff q.natDegree = 0 := Polynomial.notMem_support_iff.mp hq
    rw [hc, zero_mul]

theorem momentFunctional_X_pow_ofFn_row (s : ℕ → ℝ) (N : ℕ)
    (c : Fin N → ℝ) (i : Fin N) :
    momentFunctional s (X ^ (i : ℕ) * Polynomial.ofFn N c) =
      (momentHankelMatrix s N *ᵥ c) i := by
  rw [momentFunctional_X_pow_mul_ofFn]
  simp only [Matrix.mulVec, dotProduct, momentHankelMatrix]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem momentSectionKernel_ofFn_iff (s : ℕ → ℝ) (N : ℕ) (c : Fin N → ℝ) :
    MomentSectionKernel s N (Polynomial.ofFn N c) ↔
      momentHankelMatrix s N *ᵥ c = 0 := by
  constructor
  · intro h
    funext i
    exact (momentFunctional_X_pow_ofFn_row s N c i).symm.trans (h.2 i i.isLt)
  · intro h
    refine ⟨Polynomial.ofFn_degree_lt c, fun i hi => ?_⟩
    rw [momentFunctional_X_pow_ofFn_row s N c ⟨i, hi⟩, h]
    rfl

theorem momentSectionKernel_eq_zero_of_det_ne_zero
    {s : ℕ → ℝ} {N : ℕ} (hdet : (momentHankelMatrix s N).det ≠ 0)
    {p : ℝ[X]} (hp : MomentSectionKernel s N p) : p = 0 := by
  by_cases hp0 : p = 0
  · exact hp0
  have hd := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp.1
  have heq := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hd
  have hk : momentHankelMatrix s N *ᵥ Polynomial.toFn N p = 0 :=
    (momentSectionKernel_ofFn_iff s N _).mp (heq.symm ▸ hp)
  have hu : IsUnit (momentHankelMatrix s N) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hc := Matrix.mulVec_injective_iff_isUnit.mpr hu
    (hk.trans (Matrix.mulVec_zero _).symm)
  rw [← heq, hc, Polynomial.ofFn_zero]

theorem det_ne_zero_of_momentSectionKernel_eq_zero
    {s : ℕ → ℝ} {N : ℕ}
    (h : ∀ p, MomentSectionKernel s N p → p = 0) :
    (momentHankelMatrix s N).det ≠ 0 := by
  have hi : Function.Injective (momentHankelMatrix s N).mulVec := by
    change Function.Injective (momentHankelMatrix s N).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hp := h _ ((momentSectionKernel_ofFn_iff s N c).mpr hc)
    apply Polynomial.injective_ofFn N
    simpa only [Polynomial.ofFn_zero] using hp
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

/-- Data of the first surviving coupling after a regular head. -/
structure MomentNormalBlock (s : ℕ → ℝ) (n d : ℕ) : Prop where
  length_pos : 0 < d
  head_regular : (momentHankelMatrix s n).det ≠ 0
  vanishing : ∀ i < n + d - 1,
    momentFunctional s (X ^ i * monicMomentAdmissionPolynomial s n) = 0
  coupling_ne_zero :
    momentFunctional s (X ^ (n + d - 1) * monicMomentAdmissionPolynomial s n) ≠ 0

namespace MomentNormalBlock

variable {s : ℕ → ℝ} {n d : ℕ} (h : MomentNormalBlock s n d)
include h

/-- The complete kernel through a normal block is a truncated principal ideal. -/
theorem kernel_iff {k : ℕ} (hk : k ≤ d) (p : ℝ[X]) :
    MomentSectionKernel s (n + k) p ↔
      ∃ q : ℝ[X], q.degree < ((min k (d - k) : ℕ) : WithBot ℕ) ∧
        p = monicMomentAdmissionPolynomial s n * q := by
  let P := monicMomentAdmissionPolynomial s n
  have hP : P.Monic := monicMomentAdmissionPolynomial_monic s n
  have hPn : P.natDegree = n := monicMomentAdmissionPolynomial_natDegree s n
  have hd := h.length_pos
  constructor
  · intro hp
    let q := p /ₘ P
    let r := p %ₘ P
    have hqdeg : q.degree < (k : WithBot ℕ) := by
      by_cases hq0 : q = 0
      · simp [hq0]
      have hp0 : p ≠ 0 := by
        intro hp0
        exact hq0 (by simp [q, hp0])
      have hpnk := (natDegree_lt_iff_degree_lt hp0).mpr hp.1
      have hnp : n ≤ p.natDegree := by
        have hh : ¬p.degree < P.degree :=
          mt (divByMonic_eq_zero_iff hP).mpr hq0
        rw [degree_eq_natDegree hp0, degree_eq_natDegree hP.ne_zero, hPn] at hh
        exact_mod_cast le_of_not_gt hh
      apply (natDegree_lt_iff_degree_lt hq0).mp
      dsimp only [q]
      rw [natDegree_divByMonic p hP, hPn]
      omega
    have hlow (i : ℕ) (hi : i < n) :
        momentFunctional s (X ^ i * (P * q)) = 0 := by
      apply momentFunctional_X_pow_mul_mul_eq_zero h.vanishing
      intro a ha
      have hak : a < k := by
        by_contra hka
        exact (mem_support_iff.mp ha)
          ((degree_lt_iff_coeff_zero q k).mp hqdeg a (by omega))
      omega
    have hrker : MomentSectionKernel s n r := by
      refine ⟨?_, fun i hi => ?_⟩
      · simpa only [degree_eq_natDegree hP.ne_zero, hPn] using degree_modByMonic_lt p hP
      · have hh := hp.2 i (by omega)
        rw [← modByMonic_add_div p P, mul_add, momentFunctional_add, hlow i hi,
          add_zero] at hh
        exact hh
    have hr0 : r = 0 := momentSectionKernel_eq_zero_of_det_ne_zero h.head_regular hrker
    have hpq : p = P * q := by
      have hh := modByMonic_add_div p P
      change r + P * q = p at hh
      simpa only [hr0, zero_add] using hh.symm
    refine ⟨q, ?_, hpq⟩
    by_cases hq0 : q = 0
    · simp [hq0]
    have hqk := (natDegree_lt_iff_degree_lt hq0).mpr hqdeg
    have hqd : q.natDegree < d - k := by
      by_contra hbad
      let i := n + d - 1 - q.natDegree
      have hi : i < n + k := by dsimp only [i]; omega
      have he : i + q.natDegree = n + d - 1 := by dsimp only [i]; omega
      have hh := hp.2 i hi
      rw [hpq, momentFunctional_X_pow_mul_mul_first h.vanishing he] at hh
      exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hq0) h.coupling_ne_zero) hh
    exact (natDegree_lt_iff_degree_lt hq0).mp (lt_min hqk hqd)
  · rintro ⟨q, hq, rfl⟩
    by_cases hq0 : q = 0
    · simp [hq0, MomentSectionKernel]
    have hqnat := (natDegree_lt_iff_degree_lt hq0).mpr hq
    have hqk : q.natDegree < k := lt_of_lt_of_le hqnat (min_le_left _ _)
    have hqd : q.natDegree < d - k := lt_of_lt_of_le hqnat (min_le_right _ _)
    refine ⟨?_, fun i hi => ?_⟩
    · apply (natDegree_lt_iff_degree_lt (mul_ne_zero hP.ne_zero hq0)).mp
      rw [natDegree_mul hP.ne_zero hq0, hPn]
      omega
    · apply momentFunctional_X_pow_mul_mul_eq_zero h.vanishing
      intro a ha
      have han := le_natDegree_of_ne_zero (mem_support_iff.mp ha)
      omega

/-- The next end of the block is regular, regardless of how long its singular gap was. -/
theorem next_regular : (momentHankelMatrix s (n + d)).det ≠ 0 := by
  apply det_ne_zero_of_momentSectionKernel_eq_zero
  intro p hp
  obtain ⟨q, hq, rfl⟩ := (h.kernel_iff le_rfl p).mp hp
  have hq0 : q = 0 := by
    by_contra hne
    have hh := (natDegree_lt_iff_degree_lt hne).mpr hq
    simp only [Nat.sub_self, min_zero] at hh
    omega
  rw [hq0, mul_zero]

/-- Every proper intermediate head is singular; there are no skipped regular heads. -/
theorem intermediate_singular {k : ℕ} (hk0 : 0 < k) (hkd : k < d) :
    (momentHankelMatrix s (n + k)).det = 0 := by
  by_contra hreg
  have hp : MomentSectionKernel s (n + k) (monicMomentAdmissionPolynomial s n) := by
    apply (h.kernel_iff hkd.le _).mpr
    refine ⟨1, ?_, (mul_one _).symm⟩
    rw [Polynomial.degree_one]
    exact_mod_cast (lt_min hk0 (Nat.sub_pos_of_lt hkd))
  exact (monicMomentAdmissionPolynomial_monic s n).ne_zero
    (momentSectionKernel_eq_zero_of_det_ne_zero hreg hp)

end MomentNormalBlock

/-- Nondegeneracy produces the next normal block; no nonzero-pivot premise is added. -/
theorem exists_momentNormalBlock {s : ℕ → ℝ} (hs : NondegenerateMomentSequence s)
    {n : ℕ} (hn : (momentHankelMatrix s n).det ≠ 0) :
    ∃ d, MomentNormalBlock s n d := by
  classical
  let P := monicMomentAdmissionPolynomial s n
  have hex : ∃ i, momentFunctional s (X ^ i * P) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact (monicMomentAdmissionPolynomial_monic s n).ne_zero (hs P hh)
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  have hz : ∀ i < j, momentFunctional s (X ^ i * P) = 0 := by
    intro i hi
    exact not_ne_iff.mp (Nat.find_min hex hi)
  have hnj : n ≤ j := by
    by_contra hh
    exact hj (momentFunctional_X_pow_mul_monicMomentAdmissionPolynomial_eq_zero hn
      ⟨j, by omega⟩)
  refine ⟨j + 1 - n, ?_⟩
  have heq : n + (j + 1 - n) - 1 = j := by omega
  exact ⟨by omega, hn, heq.symm ▸ hz, heq.symm ▸ hj⟩

/-- Regular leading heads exist beyond every degree. -/
theorem cofinal_regular_momentHeads {s : ℕ → ℝ} (hs : NondegenerateMomentSequence s)
    (N : ℕ) : ∃ n ≥ N, (momentHankelMatrix s n).det ≠ 0 := by
  induction N with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ N ih =>
    obtain ⟨n, hnN, hn⟩ := ih
    obtain ⟨d, hd⟩ := exists_momentNormalBlock hs hn
    exact ⟨n + d, by have := hd.length_pos; omega, hd.next_regular⟩

/-- Every section belongs to a normal block, including singular sections. -/
theorem exists_momentNormalBlock_cover {s : ℕ → ℝ} (hs : NondegenerateMomentSequence s)
    (N : ℕ) : ∃ n d, MomentNormalBlock s n d ∧ n ≤ N ∧ N < n + d := by
  classical
  let regular := fun n => (momentHankelMatrix s n).det ≠ 0
  let n := Nat.findGreatest regular N
  have hn : regular n := Nat.findGreatest_spec (Nat.zero_le N) (by simp [regular])
  have hnN : n ≤ N := Nat.findGreatest_le N
  obtain ⟨d, hd⟩ := exists_momentNormalBlock hs hn
  refine ⟨n, d, hd, hnN, ?_⟩
  by_contra hh
  have hmax := Nat.findGreatest_is_greatest (P := regular)
    (n := N) (k := n + d) (by have := hd.length_pos; dsimp [n]; omega) (by omega)
  exact hmax hd.next_regular

/-- Normal blocks covering the same section coincide. -/
theorem MomentNormalBlock.cover_unique {s : ℕ → ℝ} {n d n' d' N : ℕ}
    (h : MomentNormalBlock s n d) (h' : MomentNormalBlock s n' d')
    (hn : n ≤ N) (hN : N < n + d) (hn' : n' ≤ N) (hN' : N < n' + d') :
    n = n' ∧ d = d' := by
  have hnn : n = n' := by
    rcases lt_trichotomy n n' with hlt | heq | hgt
    · have hz := h.intermediate_singular (k := n' - n) (by omega) (by omega)
      have he : n + (n' - n) = n' := by omega
      exact False.elim (h'.head_regular (he ▸ hz))
    · exact heq
    · have hz := h'.intermediate_singular (k := n - n') (by omega) (by omega)
      have he : n' + (n - n') = n := by omega
      exact False.elim (h.head_regular (he ▸ hz))
  subst n'
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · exact False.elim (h.coupling_ne_zero (h'.vanishing _ (by
      have := h.length_pos; omega)))
  · exact heq
  · exact False.elim (h'.coupling_ne_zero (h.vanishing _ (by
      have := h'.length_pos; omega)))

end
end HTGeometry
