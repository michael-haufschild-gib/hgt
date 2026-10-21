import GaloisForLFunctions.TransHorizonIncidenceMechanics.CharacterFourParityPairAtEveryDamping
import GaloisForLFunctions.BezoutValuationIncidence.MomentSignVisibilityAndZeroProductRelations
import GaloisForLFunctions.RHTower.EulerDeletionRemainderMobiusInversion

/-!
# The parity rows at every horizon

At horizon `N` take the character row `c_N(d) = χ₄(d) d^{-ε} 1_{d ≤ N}` and its **parity twin**
`c'_N`, the row whose Selberg coordinates are `χ₄(q) Y_N(q; c_N)` (the BVI row
`scaledSelbergRow` with the sign extension of `χ₄`). At every horizon:

* the Selberg coordinates agree up to sign, so every complete-period quadratic form of the sieve
  theory (variance, Bézout successor form, reserve, primitive energy, every lag covariance) agrees;
* every two-point translated moment agrees (two-point data are blind to signs);
* a cubic translated moment differs, through the zero-product triple `ζ₃ ζ₃ ζ₃ = 1` at the modulus
  `3`, where `χ₄(3) = -1`.

The trans-horizon receiver separates them. The pronic energy of the prefix discrepancy of `c_N` is
bounded uniformly in `N` (the truncated character still has partial sums in `{0, 1}`), while that of
`c'_N` tends to infinity with the horizon: the twin rows converge, divisor by divisor, to the positive
odd weight `c_+` of the character pair, whose drift diverges.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The rows -/

/-- `χ₄` cut at the horizon `N`. -/
def chiFourCut (N d : ℕ) : ℝ := if d ≤ N then chiFour d else 0

theorem abs_sum_range_chiFourCut_le (N x : ℕ) : |∑ d ∈ range x, chiFourCut N d| ≤ 1 := by
  have h : ∑ d ∈ range x, chiFourCut N d = ∑ d ∈ range (min x (N + 1)), chiFour d := by
    unfold chiFourCut
    rw [← sum_filter]
    congr 1
    ext d; simp only [mem_filter, mem_range]; omega
  rw [h]
  exact abs_sum_range_chiFour_le _

/-- The horizon-`N` character row `χ₄(d) d^{-ε} 1_{d ≤ N}`. -/
def chiFourRow (ε : ℝ) (N : ℕ) : ℕ → ℝ := dampedSignWeight (chiFourCut N) ε

/-- The sign extension of `χ₄`: `χ₄(q)` on odd moduli and `1` on even ones. -/
def chiFourSign (q : ℕ) : ℝ := if q % 2 = 1 then chiFour q else 1

theorem chiFourSign_mul_self (q : ℕ) : chiFourSign q * chiFourSign q = 1 := by
  unfold chiFourSign
  split_ifs with h
  · have := chiFour_sq q
    rw [if_pos h, sq] at this
    exact this
  · ring

/-- `χ₄`-sign times the character weight is the odd weight: `σ(q) χ₄(q) = 1_{odd}(q)`. -/
theorem chiFourSign_mul_dampedSignWeight (ε : ℝ) (q : ℕ) :
    chiFourSign q * dampedSignWeight chiFour ε q = dampedSignWeight oddIndicator ε q := by
  unfold chiFourSign dampedSignWeight oddIndicator
  split_ifs with h
  · rw [← mul_assoc, ← sq, chiFour_sq, if_pos h]
  · rw [chiFour_eq, if_pos (by omega)]; ring

/-- **The parity twin at horizon `N`**: Selberg coordinates `χ₄(q) Y_N(q)`. -/
def chiFourTwinRow (ε : ℝ) (N : ℕ) : ℕ → ℝ := scaledSelbergRow N (chiFourRow ε N) chiFourSign

/-! ### Identical complete-period data, separated at degree three -/

theorem selbergMultiplesCoord_chiFourTwinRow (ε : ℝ) {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (chiFourTwinRow ε N) q =
      chiFourSign q * selbergMultiplesCoord N (chiFourRow ε N) q :=
  selbergMultiplesCoord_scaledSelbergRow _ _ hq

/-- The Selberg coordinates of the pair agree up to sign at every horizon. -/
theorem sq_selbergMultiplesCoord_chiFourTwinRow (ε : ℝ) {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (chiFourTwinRow ε N) q ^ 2 =
      selbergMultiplesCoord N (chiFourRow ε N) q ^ 2 := by
  rw [selbergMultiplesCoord_chiFourTwinRow ε hq, mul_pow, sq (chiFourSign q),
    chiFourSign_mul_self, one_mul]

/-- **Two-point blindness.** Every two-point translated moment of the pair agrees. -/
theorem translatedMoment_two_chiFourTwinRow (ε : ℝ) (N : ℕ) (v : Fin 2 → ℕ) :
    SieveMoments.translatedMoment N (chiFourTwinRow ε N) v =
      SieveMoments.translatedMoment N (chiFourRow ε N) v :=
  translatedMoment_two_scaled_eq N _ chiFourSign_mul_self v

/-- Selberg coordinates of the character row: `Y_N(e) = (c_χ(e)/e) Σ_{k ≤ N/e} c_χ(k)/k`. -/
theorem selbergMultiplesCoord_chiFourRow (ε : ℝ) {N e : ℕ} (he : 0 < e) :
    selbergMultiplesCoord N (chiFourRow ε N) e =
      dampedSignWeight chiFour ε e / e * ∑ k ∈ Icc 1 (N / e), dampedSignWeight chiFour ε k / k := by
  unfold selbergMultiplesCoord
  rw [RHTower.sum_Icc_filter_dvd_reindex e N he, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hek : e * k ≤ N := by
    have := (mem_Icc.mp hk).2
    calc e * k ≤ e * (N / e) := Nat.mul_le_mul_left e this
      _ ≤ N := Nat.mul_div_le N e
  have hrow : chiFourRow ε N (e * k) = dampedSignWeight chiFour ε (e * k) := by
    simp [chiFourRow, dampedSignWeight, chiFourCut, hek]
  rw [hrow, dampedSignWeight_mul_div chiFour_mul]

/-- The partial character masses `L_X = Σ_{k ≤ X} χ₄(k) k^{-1-ε}` lie in `[1 - 2^{-ε}, 1 + 2^{-ε}]`. -/
theorem abs_chiFourPartialMass_sub_one_le {ε : ℝ} (hε : 0 < ε) {X : ℕ} (hX : 1 ≤ X) :
    |∑ k ∈ Icc 1 X, dampedSignWeight chiFour ε k / k - 1| ≤ (2 : ℝ) ^ (-ε) := by
  obtain ⟨K, rfl⟩ : ∃ K, X = 1 + K := ⟨X - 1, by omega⟩
  have hsplit : ∑ k ∈ Icc 1 (1 + K), dampedSignWeight chiFour ε k / k =
      1 + ∑ i ∈ range K, ((i + 2 : ℕ) : ℝ) ^ (-(1 + ε)) * chiFour (i + 2) := by
    have h1 : Icc 1 (1 + K) = insert 1 (Ioc 1 (1 + K)) := by
      ext d; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
    rw [h1, sum_insert (by simp), dampedSign_sum_Ioc_eq_sum_range_shift]
    have hone : dampedSignWeight chiFour ε 1 / (1 : ℕ) = 1 := by
      simp [dampedSignWeight, chiFour_eq]
    rw [hone]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [dampedSignWeight_div hε]
  have hblock := abs_sum_block_rpow_le (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ 1 + ε)
    abs_sum_range_chiFour_le (k := 2) (by norm_num) K
  rw [hsplit, add_sub_cancel_left]
  refine hblock.trans_eq ?_
  rw [show -(1 + ε) = -ε - 1 by ring, Real.rpow_sub_one (by norm_num)]
  push_cast
  ring

theorem chiFourPartialMass_pos {ε : ℝ} (hε : 0 < ε) {X : ℕ} (hX : 1 ≤ X) :
    0 < ∑ k ∈ Icc 1 X, dampedSignWeight chiFour ε k / k := by
  have h := (abs_le.mp (abs_chiFourPartialMass_sub_one_le hε hX)).1
  have h2 : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

/-- **The cubic moment separates the pair** at every horizon `N ≥ 3`, through the zero-product
triple of three primitive cube roots of unity: `Y(3)³ (1 - χ₄(3)³) = 2 Y(3)³ ≠ 0`. -/
theorem exists_translatedMoment_three_chiFourTwinRow_ne {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 3 ≤ N) :
    ∃ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (chiFourTwinRow ε N) v ≠
      SieveMoments.translatedMoment N (chiFourRow ε N) v := by
  by_contra hall
  push Not at hall
  have hζ := Complex.isPrimitiveRoot_exp 3 (by norm_num)
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑(3 : ℕ))
  have h3 : (3 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨by norm_num, hN⟩
  set τ : Fin 3 → ℂ := ![ζ, ζ, ζ]
  have hτ : τ ∈ Fintype.piFinset (fun _ : Fin 3 => responseRoots N) := by
    refine Fintype.mem_piFinset.mpr fun i => ?_
    fin_cases i <;> exact primitiveRoot_mem_responseRoots h3 hζ
  have hprod : ∏ i, τ i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [τ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← pow_two, ← pow_succ, hζ.pow_eq_one]
  have h := (translatedMoment_scaled_eq_iff N (chiFourRow ε N) chiFourSign 3).mp hall τ hτ hprod
  have hord : ∀ i, orderOf (τ i) = 3 := by
    intro i
    fin_cases i <;> exact hζ.eq_orderOf.symm
  simp only [hord, prod_const, card_univ, Fintype.card_fin] at h
  have hsign : chiFourSign 3 = -1 := by
    simp [chiFourSign, chiFour_eq]
  rw [hsign] at h
  have hY : selbergMultiplesCoord N (chiFourRow ε N) 3 ≠ 0 := by
    rw [selbergMultiplesCoord_chiFourRow ε (by norm_num)]
    have hpos := chiFourPartialMass_pos hε (X := N / 3) (by omega)
    have hc : dampedSignWeight chiFour ε 3 / (3 : ℕ) ≠ 0 := by
      have : (3 : ℝ) ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      simp [dampedSignWeight, chiFour_eq, this]
    exact mul_ne_zero hc hpos.ne'
  have : selbergMultiplesCoord N (chiFourRow ε N) 3 ^ 3 = 0 := by nlinarith [h]
  exact hY (pow_eq_zero_iff (by norm_num) |>.mp this)

/-! ### The pronic discrepancy energy at horizon `N` -/

/-- The pronic energy of the prefix discrepancy of a horizon-`N` row: the receiver energy with the
horizon-`N` harmonic mean `Y_N(1)`. -/
def horizonPronicEnergy (N : ℕ) (c : ℕ → ℝ) (T : ℕ) : ℝ :=
  weightPronicEnergy c (selbergMultiplesCoord N c 1) T

theorem tsum_chiFourRow_div (ε : ℝ) (N : ℕ) :
    ∑' d : ℕ, chiFourRow ε N d / d = selbergMultiplesCoord N (chiFourRow ε N) 1 := by
  rw [tsum_eq_sum (s := Icc 1 N) fun d hd => ?_]
  · unfold selbergMultiplesCoord
    congr 1
    ext d; simp
  · rw [mem_Icc, not_and_or] at hd
    rcases hd with hd | hd
    · have : d = 0 := by omega
      simp [this]
    · simp [chiFourRow, dampedSignWeight, chiFourCut, show ¬ d ≤ N by omega]

/-- **The character rows are uniformly paid.** Their pronic discrepancy energies are bounded
independently of the horizon. -/
theorem horizonPronicEnergy_chiFourRow_le {ε : ℝ} (hε : 0 < ε) (N T : ℕ) :
    horizonPronicEnergy N (chiFourRow ε N) T ≤
      36 * ∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε)) - 2) := by
  have h := weightPronicEnergy_dampedSign_le (by norm_num : (0 : ℝ) ≤ 1) hε
    (abs_sum_range_chiFourCut_le N) T
  rw [one_pow, mul_one] at h
  unfold horizonPronicEnergy
  rw [← tsum_chiFourRow_div]
  exact h

/-! ### The twin rows converge to the positive odd weight -/

/-- The odd weight `o(n) = 1_{odd}(n) n^{-1-ε}`. -/
private abbrev oddW (ε : ℝ) (n : ℕ) : ℝ := dampedSignWeight oddIndicator ε n / n

private theorem oddW_mul (ε : ℝ) (a b : ℕ) : oddW ε (a * b) = oddW ε a * oddW ε b :=
  dampedSignWeight_mul_div oddIndicator_mul a b

private theorem abs_oddW_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    |oddW ε n| ≤ (n : ℝ) ^ (-(1 + ε)) := by
  rw [oddW, dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  unfold oddIndicator
  split_ifs <;> simp [Real.rpow_nonneg]

private theorem oddW_nonneg {ε : ℝ} (hε : 0 < ε) (n : ℕ) : 0 ≤ oddW ε n := by
  rw [oddW, dampedSignWeight_div hε]
  unfold oddIndicator
  split_ifs <;> simp [Real.rpow_nonneg]

/-- `Σ_m μ(m) o(m)` inverts the odd mass: `(Σ_m μ(m) o(m)) O_ε = 1`. -/
theorem tsum_moebius_mul_oddW_mul_oddDampedMass {ε : ℝ} (hε : 0 < ε) :
    (∑' m : ℕ, (moebius m : ℝ) * oddW ε m) * oddDampedMass ε = 1 := by
  set f : ℕ → ℂ := fun n => ((oddW ε n : ℝ) : ℂ)
  have hpn : Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-(1 + ε))) :=
    (Real.summable_nat_rpow.mpr (by linarith)).subtype _
  have hf : Summable (fun x : ℕ+ × ℕ+ => ‖f ((x.1 : ℕ) * x.2)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      (hpn.mul_of_nonneg hpn (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    simp only [f, Complex.norm_real, Real.norm_eq_abs, oddW_mul]
    rw [abs_mul]
    exact mul_le_mul (abs_oddW_le hε _) (abs_oddW_le hε _) (abs_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h := RHTower.DeletionMixedRefinement.moebius_multiples_inversion f hf
  have hinner : ∀ p : ℕ+, (∑' n : ℕ+, f ((p : ℕ) * n)) = ((oddW ε p * oddDampedMass ε : ℝ) : ℂ) := by
    intro p
    rw [tsum_pnat_eq_tsum_of_eq_zero (f := fun n : ℕ => f ((p : ℕ) * n)) (by simp [f, oddW])]
    simp only [f, oddW_mul]
    rw [← Complex.ofReal_tsum, tsum_mul_left]
    rfl
  simp_rw [hinner] at h
  rw [tsum_pnat_eq_tsum_of_eq_zero
    (f := fun m : ℕ => (moebius m : ℂ) * ((oddW ε m * oddDampedMass ε : ℝ) : ℂ)) (by simp)] at h
  have hone : f 1 = 1 := by simp [f, oddW, dampedSignWeight, oddIndicator]
  rw [hone] at h
  have h' : ((∑' m : ℕ, (moebius m : ℝ) * (oddW ε m * oddDampedMass ε) : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_tsum]
    simpa using h
  have h'' : ∑' m : ℕ, (moebius m : ℝ) * (oddW ε m * oddDampedMass ε) = 1 := by exact_mod_cast h'
  rw [← h'', ← tsum_mul_right]
  exact tsum_congr fun m => by ring

/-- The twin row in closed form: `c'_N(d) = d Σ_{m ≤ N/d} μ(m) o(dm) L_{N/(dm)}`. -/
private theorem chiFourTwinRow_eq (ε : ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    chiFourTwinRow ε N d = (d : ℝ) * ∑ m ∈ Icc 1 (N / d), (moebius m : ℝ) *
      (oddW ε (d * m) * ∑ k ∈ Icc 1 (N / d / m), dampedSignWeight chiFour ε k / k) := by
  unfold chiFourTwinRow scaledSelbergRow RHTower.pmRamanujanResidueCoeff
  congr 1
  refine sum_congr rfl fun m hm => ?_
  dsimp only
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  rw [selbergMultiplesCoord_chiFourRow ε (Nat.mul_pos hd hm0), Nat.div_div_eq_div_mul,
    ← mul_assoc (chiFourSign (d * m)), ← mul_div_assoc, chiFourSign_mul_dampedSignWeight]

/-- **The twin rows converge to the positive odd weight**, divisor by divisor. -/
theorem tendsto_chiFourTwinRow {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    Tendsto (fun N => chiFourTwinRow ε N d) atTop (𝓝 (oddDampedTwinWeight ε d)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : ∀ N, chiFourTwinRow ε N 0 = 0 := fun N => by
      simp [chiFourTwinRow, scaledSelbergRow, RHTower.pmRamanujanResidueCoeff]
    simp only [h0]
    have : oddDampedTwinWeight ε 0 = 0 := by
      simp [oddDampedTwinWeight, dampedSignWeight, Real.zero_rpow (show -ε ≠ 0 by linarith)]
    rw [this]
    exact tendsto_const_nhds
  set L := chiFourDampedMass ε
  -- the partial masses converge to `L`
  have hLsum : HasSum (fun k : ℕ => dampedSignWeight chiFour ε k / k) L :=
    (summable_dampedSignWeight_div (by norm_num : (0 : ℝ) ≤ 1) hε abs_sum_range_chiFour_le).hasSum
  have hLX : Tendsto (fun X : ℕ => ∑ k ∈ Icc 1 X, dampedSignWeight chiFour ε k / k) atTop (𝓝 L) := by
    refine (hLsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun X => ?_
    simp only [Function.comp_apply]
    rw [dampedSign_sum_range_succ_eq_add_Icc]
    simp [dampedSignWeight]
  -- dominated convergence over the cofactor `m`
  set F : ℕ → ℕ → ℝ := fun N m => if m ∈ Icc 1 (N / d) then (moebius m : ℝ) *
      (oddW ε (d * m) * ∑ k ∈ Icc 1 (N / d / m), dampedSignWeight chiFour ε k / k) else 0
  have hFsum : ∀ N, chiFourTwinRow ε N d = (d : ℝ) * ∑' m, F N m := by
    intro N
    rw [chiFourTwinRow_eq ε N hd, tsum_eq_sum (s := Icc 1 (N / d)) fun m hm => by
      simp only [F, if_neg hm]]
    congr 1
    exact sum_congr rfl fun m hm => by simp only [F, if_pos hm]
  have hbound : ∀ N m, |F N m| ≤ 2 * (m : ℝ) ^ (-(1 + ε)) := by
    intro N m
    simp only [F]
    split_ifs with hm
    · have hm1 := (mem_Icc.mp hm)
      have hX : 1 ≤ N / d / m := (Nat.le_div_iff_mul_le hm1.1).mpr (by simpa using hm1.2)
      have hL := abs_chiFourPartialMass_sub_one_le hε hX
      have hL2 : |∑ k ∈ Icc 1 (N / d / m), dampedSignWeight chiFour ε k / k| ≤ 2 := by
        have h2 : (2 : ℝ) ^ (-ε) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
        rw [abs_le] at hL ⊢; constructor <;> linarith
      have hmu : |(moebius m : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1.1
      have hodd : |oddW ε (d * m)| ≤ (m : ℝ) ^ (-(1 + ε)) := by
        refine (abs_oddW_le hε _).trans ?_
        push_cast
        exact Real.rpow_le_rpow_of_nonpos hm0 (by nlinarith) (by linarith)
      rw [abs_mul, abs_mul]
      calc |(moebius m : ℝ)| * (|oddW ε (d * m)| *
            |∑ k ∈ Icc 1 (N / d / m), dampedSignWeight chiFour ε k / k|)
          ≤ 1 * ((m : ℝ) ^ (-(1 + ε)) * 2) :=
            mul_le_mul hmu (mul_le_mul hodd hL2 (abs_nonneg _)
              (Real.rpow_nonneg (Nat.cast_nonneg m) _)) (by positivity) (by norm_num)
        _ = 2 * (m : ℝ) ^ (-(1 + ε)) := by ring
    · simp only [abs_zero]; positivity
  have hlim : ∀ m, Tendsto (fun N => F N m) atTop (𝓝 ((moebius m : ℝ) * (oddW ε (d * m) * L))) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F]
    have hev : ∀ᶠ N in atTop, m ∈ Icc 1 (N / d) := by
      filter_upwards [eventually_ge_atTop (d * m)] with N hN
      exact mem_Icc.mpr ⟨hm, (Nat.le_div_iff_mul_le hd).mpr (by linarith [mul_comm d m])⟩
    have hdiv : Tendsto (fun N => N / d / m) atTop atTop :=
      (Nat.tendsto_div_const_atTop hm.ne').comp (Nat.tendsto_div_const_atTop hd.ne')
    have hmain := ((hLX.comp hdiv).const_mul (oddW ε (d * m))).const_mul (moebius m : ℝ)
    refine hmain.congr' ?_
    filter_upwards [hev] with N hN
    simp only [F, if_pos hN, Function.comp_apply]
  have hdom := tendsto_tsum_of_dominated_convergence
    (bound := fun m : ℕ => 2 * ((m : ℕ) : ℝ) ^ (-(1 + ε)))
    ((Real.summable_nat_rpow.mpr (by linarith : -(1 + ε) < -1)).mul_left 2) hlim
    (Eventually.of_forall fun N m => by simpa [Real.norm_eq_abs] using hbound N m)
  -- identify the limit with the positive odd weight
  have hlimit : (d : ℝ) * ∑' m, (moebius m : ℝ) * (oddW ε (d * m) * L) = oddDampedTwinWeight ε d := by
    have hO := (oddDampedMass_pos hε).ne'
    have hinv := tsum_moebius_mul_oddW_mul_oddDampedMass hε
    have hrw : ∀ m, (moebius m : ℝ) * (oddW ε (d * m) * L) =
        (oddW ε d * L) * ((moebius m : ℝ) * oddW ε m) := fun m => by rw [oddW_mul]; ring
    simp_rw [hrw]
    rw [tsum_mul_left]
    have hT : ∑' m : ℕ, (moebius m : ℝ) * oddW ε m = 1 / oddDampedMass ε := by
      rw [eq_div_iff hO]; exact hinv
    rw [hT, oddDampedTwinWeight]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [oddW]
    field_simp
    rfl
  rw [← hlimit]
  refine (hdom.const_mul (d : ℝ)).congr fun N => ?_
  rw [hFsum]

/-- The harmonic means converge: `Y_N(1; c'_N) = L_N → L_ε`. -/
theorem tendsto_selbergMultiplesCoord_one_chiFourTwinRow {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => selbergMultiplesCoord N (chiFourTwinRow ε N) 1) atTop
      (𝓝 (chiFourDampedMass ε)) := by
  have hLsum : HasSum (fun k : ℕ => dampedSignWeight chiFour ε k / k) (chiFourDampedMass ε) :=
    (summable_dampedSignWeight_div (by norm_num : (0 : ℝ) ≤ 1) hε abs_sum_range_chiFour_le).hasSum
  have hLX := hLsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine (hLX.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Function.comp_apply]
  rw [selbergMultiplesCoord_chiFourTwinRow ε (mem_Icc.mpr ⟨le_refl 1, hN⟩),
    selbergMultiplesCoord_chiFourRow ε one_pos, dampedSign_sum_range_succ_eq_add_Icc]
  have hs1 : chiFourSign 1 = 1 := by simp [chiFourSign, chiFour_eq]
  have hχ1 : chiFour 1 = 1 := by simp [chiFour_eq]
  simp [hs1, hχ1, dampedSignWeight]

/-- The receiver energy at a fixed cutoff is continuous in the weight and the mean. -/
theorem tendsto_weightPronicEnergy_of_pointwise {c : ℕ → ℕ → ℝ} {c₀ : ℕ → ℝ} {m : ℕ → ℝ} {m₀ : ℝ}
    (hc : ∀ d, Tendsto (fun N => c N d) atTop (𝓝 (c₀ d))) (hm : Tendsto m atTop (𝓝 m₀)) (T : ℕ) :
    Tendsto (fun N => weightPronicEnergy (c N) (m N) T) atTop (𝓝 (weightPronicEnergy c₀ m₀ T)) := by
  unfold weightPronicEnergy weightCenteredPrefix
  refine tendsto_finsetSum _ fun n _ => ?_
  refine Tendsto.div_const (Tendsto.pow (Tendsto.sub ?_ (hm.mul_const _)) 2) _
  exact tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun d _ => hc d

/-- **The twin rows are unpaid.** Their pronic discrepancy energies tend to infinity with the
horizon, for every `0 < ε ≤ 1/2`. -/
theorem eventually_lt_horizonPronicEnergy_chiFourTwinRow {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (C : ℝ) : ∀ᶠ N in atTop, ∃ T, C < horizonPronicEnergy N (chiFourTwinRow ε N) T := by
  obtain ⟨T, hT⟩ := ((chiFour_parityPair hε hε2).2.2.2.2.eventually_gt_atTop C).exists
  have hconv := tendsto_weightPronicEnergy_of_pointwise (tendsto_chiFourTwinRow hε)
    (tendsto_selbergMultiplesCoord_one_chiFourTwinRow hε) T
  filter_upwards [hconv.eventually (lt_mem_nhds hT)] with N hN
  exact ⟨T, hN⟩

/-- **The parity rows at every horizon.** For `0 < ε ≤ 1/2`: at every horizon `N` the character
row and its twin have Selberg coordinates equal up to sign and identical two-point translated
moments; a cubic translated moment separates them (`N ≥ 3`); the character rows have uniformly
bounded pronic discrepancy energy while that of the twins tends to infinity with `N`. -/
theorem chiFour_parityRows {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ N q, q ∈ Icc 1 N → selbergMultiplesCoord N (chiFourTwinRow ε N) q ^ 2 =
        selbergMultiplesCoord N (chiFourRow ε N) q ^ 2) ∧
    (∀ N (v : Fin 2 → ℕ), SieveMoments.translatedMoment N (chiFourTwinRow ε N) v =
        SieveMoments.translatedMoment N (chiFourRow ε N) v) ∧
    (∀ N, 3 ≤ N → ∃ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (chiFourTwinRow ε N) v ≠
        SieveMoments.translatedMoment N (chiFourRow ε N) v) ∧
    (∃ C : ℝ, ∀ N T, horizonPronicEnergy N (chiFourRow ε N) T ≤ C) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T, C < horizonPronicEnergy N (chiFourTwinRow ε N) T) :=
  ⟨fun _ _ hq => sq_selbergMultiplesCoord_chiFourTwinRow ε hq,
    translatedMoment_two_chiFourTwinRow ε,
    fun _ hN => exists_translatedMoment_three_chiFourTwinRow_ne hε hN,
    ⟨_, horizonPronicEnergy_chiFourRow_le hε⟩,
    eventually_lt_horizonPronicEnergy_chiFourTwinRow hε hε2⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
