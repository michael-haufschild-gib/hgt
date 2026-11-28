import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.ParConsts

/-! The size bounds for the family imply the numerical hypotheses
of the irreducible-row count at each auxiliary prime. -/

noncomputable section

open WindowedLandauTheory.MainNotions WindowedLandauTheory.BasicNotions

namespace WindowedLandauTheory.ConcN

/-- Numerical ranges for one of the two auxiliary primes. -/
def SizesAt (x ε Cs : ℝ) (f m N g q₁ d : ℕ) : Prop :=
  Real.exp (8 * x ^ ε) ≤ (g : ℝ) ∧ x ^ 2 ≤ (f : ℝ) ∧ (f : ℝ) ≤ x ^ Cs ∧ (m : ℝ) ≤ x ^ Cs ∧
    100 ≤ N ∧ (N : ℝ) ≤ x ^ Cs ∧ Real.exp (x ^ (ε / 6)) ≤ ((min q₁ d : ℕ) : ℝ)

def SizesRec (D : D7) (x ε Cs : ℝ) : Prop :=
  ∀ j : Fin 2, SizesAt x ε Cs D.R.f D.R.m D.R.r (D.host.g j) D.host.q D.host.d

private theorem exp_le_nat_of_le_log {s : ℝ} {a : ℕ}
    (hs : 0 < s) (h : s ≤ Real.log a) : Real.exp s ≤ a := by
  have ha : (0 : ℝ) < a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [Nat.cast_zero, Real.log_zero] at h
      exact (hs.not_ge h).elim
    · exact_mod_cast ha
  exact (Real.exp_le_exp.mpr h).trans_eq (Real.exp_log ha)

/-- Bounds on the family scale, ranks and selected primes yield the
numerical ranges needed by the irreducible-row count. -/
private theorem sizesAt_of_scale {x ε z Cs : ℝ} {n f m k r g q d : ℕ}
    (hx4 : 4 ≤ x) (hε : 0 < ε) (hε' : ε < 1 / 52) (hz : 0 < z) (hze : z ≤ ε)
    (hCs : 6 ≤ Cs) (hnf : n ≤ f) (hfk : f ≤ k) (hmf : m ≤ f) (hkr : k ≤ r) (hrk : r ≤ 2 * k)
    (hn : x ^ (2 + 8 * ε - ε / 100) ≤ (n : ℝ))
    (hk : x ^ (9 / 2 + 10 * ε - ε / 100) ≤ (k : ℝ) ∧
      (k : ℝ) ≤ x ^ (9 / 2 + 10 * ε + ε / 100))
    (hq : x ^ (z / 6) ≤ Real.log q) (hd : x ^ (z / 5 - z / 100) ≤ Real.log d)
    (hg : ((k : ℝ) * Real.exp (x ^ ε)) ^ 8 ≤ (g : ℝ)) :
    SizesAt x z Cs f m r g q d := by
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 4).trans hx4
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hkU : (k : ℝ) ≤ x ^ (5 : ℝ) :=
    hk.2.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε']))
  have hkL : (256 : ℝ) ≤ k := by
    calc
      256 = (4 : ℝ) ^ (4 : ℝ) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      _ ≤ x ^ (4 : ℝ) := Real.rpow_le_rpow (by norm_num) hx4 (by norm_num)
      _ ≤ x ^ (9 / 2 + 10 * ε - ε / 100) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε])
      _ ≤ k := hk.1
  have hk100 : 100 ≤ k := (by norm_num : (100 : ℕ) ≤ 256).trans (by exact_mod_cast hkL)
  have hfU : (f : ℝ) ≤ x ^ Cs :=
    (Nat.cast_le.mpr hfk).trans (hkU.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hCs])))
  have hmin : Real.exp (x ^ (z / 6)) ≤ ((min q d : ℕ) : ℝ) := by
    have hp := Real.rpow_pos_of_pos hx0 (z / 6)
    have hzd : x ^ (z / 6) ≤ x ^ (z / 5 - z / 100) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hz])
    rw [Nat.cast_min]
    exact le_min (exp_le_nat_of_le_log hp hq) (exp_le_nat_of_le_log hp (hzd.trans hd))
  refine ⟨?_, ?_, hfU, (Nat.cast_le.mpr hmf).trans hfU, hk100.trans hkr, ?_, hmin⟩
  · have hk1 : (1 : ℝ) ≤ k := (by norm_num : (1 : ℝ) ≤ 256).trans hkL
    have he := Real.rpow_le_rpow_of_exponent_le hx1 hze
    calc
      Real.exp (8 * x ^ z) ≤ Real.exp (8 * x ^ ε) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he (by norm_num))
      _ = Real.exp (x ^ ε) ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ ((k : ℝ) * Real.exp (x ^ ε)) ^ 8 :=
        pow_le_pow_left₀ (Real.exp_pos _).le (le_mul_of_one_le_left (Real.exp_pos _).le hk1) _
      _ ≤ g := hg
  · rw [← Real.rpow_two]
    exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hε])).trans
      (hn.trans (Nat.cast_le.mpr hnf))
  · have hr : (r : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hrk
    calc
      (r : ℝ) ≤ 2 * (k : ℝ) := hr
      _ ≤ 2 * x ^ (5 : ℝ) := mul_le_mul_of_nonneg_left hkU (by norm_num)
      _ ≤ x ^ (6 : ℝ) := by
        rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one, mul_comm 2 (x ^ (5 : ℝ))]
        exact mul_le_mul_of_nonneg_left ((by norm_num : (2 : ℝ) ≤ 4).trans hx4) (Real.rpow_nonneg hx0.le _)
      _ ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 hCs

theorem sizesRec_at {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (hx4 : 4 ≤ x)
    (i : Fm.Ix x) {Cs : ℝ} (hCs : 6 ≤ Cs) : SizesRec (Fm.D x i) x Fm.ez Cs := by
  let D := Fm.D x i
  let L := Fm.L x i
  have hs : MainNotions.SizesAt L := Fm.sizes x hx i
  obtain ⟨hN, -, hK, -, -, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hs
  have hx' : L.sc.x = x := Fm.L_x x i hx
  have hε' : L.sc.eps = eps := Fm.L_eps x i
  have hz' : L.sc.ez = Fm.ez := Fm.toFamCore.L_ez x i
  have hε : 0 < eps := hε' ▸ L.sc.eps_pos
  have he : eps < 1 / 52 := hε' ▸ L.sc.eps_lt
  have hJ := Fm.toFamCore.one_le_J
  have hz : 0 < Fm.ez := div_pos hε (zero_lt_one.trans_le hJ)
  have hze : Fm.ez ≤ eps := div_le_self hε.le hJ
  simp only [SizeN, SizeK, SizeQD, SizeG, szTh, hx', hε', hz', Scale.b, Scale.L] at hN hK hQD hG
  have hnf : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
  have hfk : D.R.f ≤ D.R.k := by simpa only [Ranks.f, Ranks.n] using D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by simpa only [Ranks.f, Ranks.n] using D.R.m_le_f
  have hm2 := D.R.two_le_m
  have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have hrk : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
  intro j
  exact sizesAt_of_scale hx4 hε he hz hze hCs hnf hfk hmf hkr hrk hN.1 hK hQD.1 hQD.2.2.2.1 (hG j j).1

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.sizesRec_at
