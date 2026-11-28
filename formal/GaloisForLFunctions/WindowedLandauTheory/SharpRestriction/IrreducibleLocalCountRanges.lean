import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.IrreducibleCountSizes
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

/-! The two counting primes split with the required congruences
and lie in the numerical ranges for the local row estimates. -/

noncomputable section

open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace WindowedLandauTheory.ConcN

def RangeW (D : D7) : Prop := 100 ≤ D.R.r ∧ ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k

theorem tieAdmG_holds (D : D7) : TieAdmG D := fun k =>
  ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

variable {D : D7}

theorem host_facts (hA : TieAdmG D) (k : Fin 2) :
    D.host.q.Prime ∧ D.host.d.Prime ∧ D.host.q ≠ D.host.d ∧ D.host.q ≠ 2 ∧ D.host.d ≠ 2 ∧
      16 ≤ max D.host.q D.host.d ∧ 16 ∣ D.host.g k - 1 ∧ D.host.q ∣ D.host.g k - 1 ∧
      D.host.d ∣ D.host.g k - 1 := by
  have hadm := hA k
  unfold NTypes.admissible at hadm
  have hmod : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := hadm.2.2.2
  have hM : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have h := Nat.dvd_sub_mod (n := D.host.QS * D.host.q * D.host.d) (D.host.g k)
    rwa [hmod] at h
  have h16 : 16 ∣ D.host.QS := by
    have h := (Nat.pow_dvd_pow 2 (show 4 ≤ D.R.toFrame.e + 2 by have := D.host.two_le_e; omega)).trans
      D.host.tower_dvd
    simpa using h
  have h2 : 2 ∣ D.host.QS := (show 2 ∣ 16 by norm_num).trans h16
  have hc : Nat.Coprime 2 (D.host.q * D.host.d) := Nat.Coprime.coprime_dvd_left h2 D.host.QS_coprime
  have hq2 : D.host.q ≠ 2 := by
    intro h
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_right D.host.q D.host.d) hc
    rw [h] at this
    exact (by norm_num [Nat.Coprime] : ¬ Nat.Coprime 2 2) this
  have hd2 : D.host.d ≠ 2 := by
    intro h
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_left D.host.d D.host.q) hc
    rw [h] at this
    exact (by norm_num [Nat.Coprime] : ¬ Nat.Coprime 2 2) this
  have hbig : 16 ≤ max D.host.q D.host.d := by
    have hq := D.host.qd_big.1
    have hr : 6 ≤ D.R.r := by
      have e1 : D.R.r = D.R.k + D.R.m - 1 := rfl
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    have ht : 11 ≤ D.R.t := by
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      have := D.R.rank_add_five_le
      omega
    have hTR : 11 * 6 ≤ D.R.t * D.R.r := Nat.mul_le_mul ht hr
    have e2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := Nat.mul_assoc _ _ _
    rw [e2] at hq
    exact le_max_of_le_left (by omega)
  refine ⟨?_, ?_, ?_, hq2, hd2, hbig, (h16.trans (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).trans hM,
    (dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hM, (dvd_mul_left _ _).trans hM⟩
  · obtain ⟨x1, -, -⟩ := D.host.hyp
    exact x1
  · obtain ⟨-, x2, -⟩ := D.host.hyp
    exact x2
  · obtain ⟨-, -, x3, x4, -⟩ := D.host.hyp
    intro h
    rw [h] at x3
    omega

theorem rangeW_of_sizes {x ε Cs : ℝ} (h : SizesRec D x ε Cs) (hx : 3 / 2 ≤ x ^ ε) : RangeW D := by
  unfold SizesRec SizesAt at h
  unfold RangeW
  refine ⟨(h 0).2.2.2.2.1, fun k => ?_⟩
  have hg := (h k).1
  have h2 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have h12 : Real.exp 1 ^ 12 ≤ Real.exp (8 * x ^ ε) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have h3 : (2 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h2 12
  have h4 : (2 : ℝ) ^ 12 ≤ (D.host.g k : ℝ) := h3.trans (h12.trans hg)
  exact_mod_cast h4

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.host_facts
#print axioms WindowedLandauTheory.ConcN.rangeW_of_sizes
