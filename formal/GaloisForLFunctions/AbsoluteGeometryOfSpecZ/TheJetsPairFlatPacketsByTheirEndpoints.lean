import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGluingIndexIsTheSelfEnergyOfTheJets
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheDegreePointsCarryWeilsArchimedeanDiagonal

/-!
# The jets pair flat packets by their endpoints

The finite part of the jets on the degree points is computed on step packets. For the flat
packets on `[1, A]` and `[1, B]`, `A ≤ B`, the off-diagonal pairing of the jets is

  `X(A, B) = Σ_{n ≤ A} Σ_{m ≤ B, m ≠ n} ½(1/|m − n| + 1/(m + n))`.

* **Closed form** (`jetCross_eq`): with `S(M) = M·H_M − M = Σ_{j < M} H_j`,
  `X(A, B) = ½(S(B) − S(B − A) + S(B + A + 1) − S(B + 1)) − (3/4)·H_A`.
* **The finite part** (`tendsto_jetCross_sub_counterterm_div`): for `1 ≤ a ≤ b`,
  `(X(aN, bN) − Σ_{n ≤ aN} log(n/2π))/N → W(a, b)`,
  `W(a, b) = ½((b + a) log(b + a) − (b − a) log(b − a)) + a(γ + log 2π − log a)`;
  `W(a, a) = a(γ + log 4π)` (`flatPairing_self`).
* **Windows** (`windowEnergy_eq`, `tendsto_windowEnergy_sub_counterterm_div`): the energy of the
  jets inside `(A, B]` is `X(B, B) − 2X(A, B) + X(A, A)`, and with the counterterm `log(n/2π)` on
  `(aN, bN]` its finite part per degree point of the scale is `W(b, b) − 2W(a, b) + W(a, a)`.

The counterterm sits on the overlap of the two packets only. The limit is a function of the sums
and differences of the endpoints through `x log x`.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### The pairing of two flat packets -/

/-- The pairing of the jets between the flat packets on `[1, A]` and `[1, B]`, without the
diagonal. -/
def jetCross (A B : ℕ) : ℝ := ∑ n ∈ Icc 1 A, ∑ m ∈ (Icc 1 B).erase n, jetKernel m n

theorem jetCross_comm (A B : ℕ) : jetCross A B = jetCross B A := by
  unfold jetCross
  rw [Finset.sum_comm' (s' := fun m => (Icc 1 A).erase m) (t' := Icc 1 B) (fun n m => by
    simp only [Finset.mem_erase]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨Ne.symm h2, h1⟩, h3⟩,
      fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, Ne.symm h1, h3⟩⟩)]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => jetKernel_comm m n

/-- `S(M) = M·H_M − M`, the sum of the harmonic numbers below `M`. -/
def harmSum (M : ℕ) : ℝ := (M : ℝ) * harm M - M

theorem sum_range_harm_add (K A : ℕ) :
    ∑ j ∈ range A, harm (K + j) = harmSum (K + A) - harmSum K := by
  have h := Finset.sum_range_add harm K A
  rw [sum_range_harm, sum_range_harm] at h
  unfold harmSum
  linarith

theorem harmSum_succ (M : ℕ) : harmSum (M + 1) = harmSum M + harm M := by
  have h := sum_range_harm_add M 1
  rw [Finset.sum_range_one, add_zero] at h
  linarith

/-- **The pairing of two flat packets in closed form.** -/
theorem jetCross_eq {A B : ℕ} (hAB : A ≤ B) :
    jetCross A B =
      (harmSum B - harmSum (B - A) + (harmSum (B + 1 + A) - harmSum (B + 1))) / 2 -
        3 / 4 * harm A := by
  have hrow : jetCross A B =
      ∑ n ∈ Icc 1 A, ((harm (B - n) + harm (B + n)) / 2 - 3 / 4 * (1 / (n : ℝ))) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 := (mem_Icc.mp hn).1
    have hnB : n ≤ B := (mem_Icc.mp hn).2.trans hAB
    have hsplit : (Icc 1 B).erase n = Ico 1 n ∪ Ioc n B := by
      ext k
      simp only [mem_erase, mem_Icc, mem_union, mem_Ico, mem_Ioc]
      omega
    have hdisj : Disjoint (Ico 1 n) (Ioc n B) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [mem_Ico, mem_Ioc] at hk hk'
      omega
    rw [hsplit, Finset.sum_union hdisj, sum_jetKernel_row hn1 hnB]
    ring
  have h1 : ∑ n ∈ Icc 1 A, harm (B - n) = harmSum B - harmSum (B - A) := by
    rw [sum_Icc_one_eq_sum_range]
    calc ∑ k ∈ range A, harm (B - (1 + k))
        = ∑ k ∈ range A, harm (B - A + (A - 1 - k)) :=
          Finset.sum_congr rfl fun k hk => by
            have hk' := mem_range.mp hk
            congr 1
            omega
      _ = ∑ j ∈ range A, harm (B - A + j) :=
          Finset.sum_range_reflect (fun j => harm (B - A + j)) A
      _ = harmSum (B - A + A) - harmSum (B - A) := sum_range_harm_add _ _
      _ = harmSum B - harmSum (B - A) := by rw [Nat.sub_add_cancel hAB]
  have h2 : ∑ n ∈ Icc 1 A, harm (B + n) = harmSum (B + 1 + A) - harmSum (B + 1) := by
    rw [sum_Icc_one_eq_sum_range, ← sum_range_harm_add]
    exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_assoc]
  have h3 : ∑ n ∈ Icc 1 A, 1 / (n : ℝ) = harm A := by
    rw [sum_Icc_one_eq_sum_range, harm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
  rw [hrow, Finset.sum_sub_distrib, ← Finset.mul_sum, h3, ← Finset.sum_div,
    Finset.sum_add_distrib, h1, h2]

/-! ### The finite part -/

/-- `S(xN)/N − x log N → x(log x + γ − 1)`. -/
theorem tendsto_harmSum_mul_div (x : ℕ) :
    Tendsto (fun N : ℕ => harmSum (x * N) / N - x * Real.log N) atTop
      (𝓝 (x * (Real.log x + Real.eulerMascheroniConstant - 1))) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [harmSum]
  · have hx' : (0 : ℝ) < x := by exact_mod_cast hx
    have hxN : Tendsto (fun N : ℕ => x * N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hx) tendsto_id
    have h := ((tendsto_harm_sub_log.comp hxN).const_mul (x : ℝ)).add_const
      ((x : ℝ) * Real.log x - x)
    have hval : (x : ℝ) * Real.eulerMascheroniConstant + ((x : ℝ) * Real.log x - x) =
        x * (Real.log x + Real.eulerMascheroniConstant - 1) := by ring
    rw [hval] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Function.comp_apply, harmSum]
    rw [show ((x * N : ℕ) : ℝ) = (x : ℝ) * N by push_cast; ring,
      Real.log_mul hx'.ne' hN'.ne']
    field_simp
    ring

/-- `H_{xN}/N → 0`. -/
theorem tendsto_harm_mul_div (x : ℕ) :
    Tendsto (fun N : ℕ => harm (x * N) / N) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [harm_zero]
  · have hx' : (0 : ℝ) < x := by exact_mod_cast hx
    have hxN : Tendsto (fun N : ℕ => x * N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hx) tendsto_id
    have hM : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h1 := (tendsto_harm_sub_log.comp hxN).div_atTop hM
    have h2 : Tendsto (fun N : ℕ => Real.log x / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hM
    have h := (h1.add h2).add tendsto_log_div_nat
    rw [add_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Function.comp_apply]
    rw [show ((x * N : ℕ) : ℝ) = (x : ℝ) * N by push_cast; ring,
      Real.log_mul hx'.ne' hN'.ne']
    field_simp
    ring

/-- The finite part of the pairing of the flat packets on `[1, aN]` and `[1, bN]`, per degree
point of the scale `N`. -/
def flatPairing (a b : ℕ) : ℝ :=
  (((b : ℝ) + a) * Real.log ((b : ℝ) + a) - ((b : ℝ) - a) * Real.log ((b : ℝ) - a)) / 2 +
    a * (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) - Real.log a)

theorem flatPairing_self {a : ℕ} (ha : 1 ≤ a) :
    flatPairing a a = a * (Real.eulerMascheroniConstant + Real.log (4 * Real.pi)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h4 : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [show (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) by ring,
      Real.log_mul (x := 2) (y := 2 * Real.pi) (by norm_num) (by positivity)]
  unfold flatPairing
  rw [sub_self, zero_mul, sub_zero, ← two_mul, Real.log_mul (by norm_num) ha'.ne', h4]
  ring

/-- **The finite part of the jets on two flat packets**: with the counterterm `log(n/2π)` on the
overlap, the pairing per degree point of the scale tends to `W(a, b)`. -/
theorem tendsto_jetCross_sub_counterterm_div {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ =>
        (jetCross (a * N) (b * N) - ∑ n ∈ Icc 1 (a * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N)
      atTop (𝓝 (flatPairing a b)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have haN : Tendsto (fun N : ℕ => a * N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N ha) tendsto_id
  have T6 := ((tendsto_log_factorial_div_sub.comp haN).const_mul (a : ℝ)).add_const
    ((a : ℝ) * Real.log a - a)
  have hlim := (((((tendsto_harmSum_mul_div b).sub (tendsto_harmSum_mul_div (b - a))).add
    (((tendsto_harmSum_mul_div (b + a)).add (tendsto_harm_mul_div (b + a))).sub
      ((tendsto_harmSum_mul_div b).add (tendsto_harm_mul_div b)))).div_const 2).sub
    ((tendsto_harm_mul_div a).const_mul (3 / 4))).sub T6
  have hlim' := hlim.add_const ((a : ℝ) * Real.log (2 * Real.pi))
  have hval : ((b : ℝ) * (Real.log b + Real.eulerMascheroniConstant - 1) -
      ((b - a : ℕ) : ℝ) * (Real.log ((b - a : ℕ) : ℝ) + Real.eulerMascheroniConstant - 1) +
      (((b + a : ℕ) : ℝ) * (Real.log ((b + a : ℕ) : ℝ) + Real.eulerMascheroniConstant - 1) + 0 -
        ((b : ℝ) * (Real.log b + Real.eulerMascheroniConstant - 1) + 0))) / 2 - 3 / 4 * 0 -
      ((a : ℝ) * 0 + ((a : ℝ) * Real.log a - a)) + (a : ℝ) * Real.log (2 * Real.pi) =
      flatPairing a b := by
    unfold flatPairing
    rw [Nat.cast_sub hab, Nat.cast_add]
    ring
  rw [hval] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : a * N ≤ b * N := Nat.mul_le_mul_right N hab
  simp only [Function.comp_apply]
  rw [jetCross_eq hle, sum_log_div_two_pi, ← Nat.sub_mul,
    show b * N + 1 + a * N = (b + a) * N + 1 by ring, harmSum_succ, harmSum_succ,
    show ((a * N : ℕ) : ℝ) = (a : ℝ) * N by push_cast; ring, Real.log_mul ha'.ne' hN'.ne',
    Nat.cast_sub hab, Nat.cast_add]
  field_simp
  ring

/-! ### Windows -/

/-- The energy of the jets inside the window `(A, B]`. -/
def windowEnergy (A B : ℕ) : ℝ := ∑ n ∈ Ioc A B, ∑ m ∈ (Ioc A B).erase n, jetKernel m n

/-- **Inclusion and exclusion**: the energy of a window from the pairings of flat packets. -/
theorem windowEnergy_eq {A B : ℕ} (hAB : A ≤ B) :
    windowEnergy A B = jetCross B B - 2 * jetCross A B + jetCross A A := by
  have hI : Icc 1 B = Icc 1 A ∪ Ioc A B := by
    ext k
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 A) (Ioc A B) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_Icc, mem_Ioc] at hk hk'
    omega
  have hin : ∀ n, ∑ m ∈ (Icc 1 B).erase n, jetKernel m n =
      ∑ m ∈ (Icc 1 A).erase n, jetKernel m n + ∑ m ∈ (Ioc A B).erase n, jetKernel m n := by
    intro n
    rw [hI, Finset.erase_union_distrib,
      Finset.sum_union (hd.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))]
  have hout : ∀ f : ℕ → ℝ, ∑ n ∈ Icc 1 B, f n = ∑ n ∈ Icc 1 A, f n + ∑ n ∈ Ioc A B, f n := by
    intro f
    rw [hI, Finset.sum_union hd]
  have e1 : jetCross B B =
      jetCross A B + ∑ n ∈ Ioc A B, ∑ m ∈ (Icc 1 B).erase n, jetKernel m n :=
    hout fun n => ∑ m ∈ (Icc 1 B).erase n, jetKernel m n
  have e2 : ∑ n ∈ Ioc A B, ∑ m ∈ (Icc 1 B).erase n, jetKernel m n =
      ∑ n ∈ Ioc A B, ∑ m ∈ (Icc 1 A).erase n, jetKernel m n + windowEnergy A B := by
    rw [windowEnergy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => hin n
  have e3 : jetCross B A =
      jetCross A A + ∑ n ∈ Ioc A B, ∑ m ∈ (Icc 1 A).erase n, jetKernel m n :=
    hout fun n => ∑ m ∈ (Icc 1 A).erase n, jetKernel m n
  rw [jetCross_comm B A] at e3
  linarith

/-- **The finite part of the jets on a window**: with the counterterm `log(n/2π)` on `(aN, bN]`,
the energy per degree point of the scale tends to `W(b, b) − 2W(a, b) + W(a, a)`. -/
theorem tendsto_windowEnergy_sub_counterterm_div {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ =>
        (windowEnergy (a * N) (b * N) -
          ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi))) / N)
      atTop (𝓝 (flatPairing b b - 2 * flatPairing a b + flatPairing a a)) := by
  have h := ((tendsto_jetCross_sub_counterterm_div (ha.trans hab) le_rfl).sub
    ((tendsto_jetCross_sub_counterterm_div ha hab).const_mul 2)).add
    (tendsto_jetCross_sub_counterterm_div ha le_rfl)
  refine h.congr fun N => ?_
  have hle : a * N ≤ b * N := Nat.mul_le_mul_right N hab
  have hI : Icc 1 (b * N) = Icc 1 (a * N) ∪ Ioc (a * N) (b * N) := by
    ext k
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hd : Disjoint (Icc 1 (a * N)) (Ioc (a * N) (b * N)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [mem_Icc, mem_Ioc] at hk hk'
    omega
  have hct : ∑ n ∈ Icc 1 (b * N), Real.log ((n : ℝ) / (2 * Real.pi)) =
      ∑ n ∈ Icc 1 (a * N), Real.log ((n : ℝ) / (2 * Real.pi)) +
        ∑ n ∈ Ioc (a * N) (b * N), Real.log ((n : ℝ) / (2 * Real.pi)) := by
    rw [hI, Finset.sum_union hd]
  rw [windowEnergy_eq hle, hct]
  ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
