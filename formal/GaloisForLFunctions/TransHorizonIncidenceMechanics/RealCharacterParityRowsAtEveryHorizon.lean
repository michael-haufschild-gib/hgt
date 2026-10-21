import GaloisForLFunctions.TransHorizonIncidenceMechanics.LogarithmicMomentsAreACompleteReceiverInvariant
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CharacterFourParityRowsAtEveryHorizon
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CubicMomentsPinTheParityOfOddRows

/-!
# The parity rows of every real character at every horizon

For a real non-principal character `χ` mod `q` take the horizon-`N` row `c_N(d) = χ(d)d^{-ε}1_{d≤N}`
and its **parity twin** `c'_N`, the row whose Selberg coordinates are `χ̂(e) Y_N(e)` with the sign
extension `χ̂(e) = χ(e)` (or `1` where `χ(e) = 0`). At every horizon the Selberg coordinates agree up
to sign and every two-point translated moment agrees; at all large horizons a cubic translated
moment separates them, at an odd modulus `n₀` with `χ(n₀) = −1` (zero-product triple
`ζ ζ ζ^{n₀−2} = 1`). The rows of `χ` keep their partial sums below `q`, so their pronic discrepancy
energies are bounded uniformly in the horizon; the twin rows converge divisor by divisor to the
signed positive twin `(L/O) 1_{(d,q)=1} d^{-ε}` (Möbius inversion of the unit mass `O`), whose receiver
diverges at every `ε ≤ 1/2`. **Every real character carries parity rows at every horizon**; the
separating additive observable is the cubic translated moment at one inert odd modulus.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

/-! ### The rows -/

/-- `χ` cut at the horizon `N`. -/
def charCut (χ : MulChar (ZMod q) ℤ) (N d : ℕ) : ℝ := if d ≤ N then charSign χ d else 0

theorem abs_sum_range_charCut_le {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) (N x : ℕ) :
    |∑ d ∈ range x, charCut χ N d| ≤ q := by
  have h : ∑ d ∈ range x, charCut χ N d = ∑ d ∈ range (min x (N + 1)), charSign χ d := by
    unfold charCut
    rw [← sum_filter]
    congr 1
    ext d; simp only [mem_filter, mem_range]; omega
  rw [h]
  exact abs_sum_range_charSign_le hχ _

/-- The horizon-`N` character row `χ(d) d^{-ε} 1_{d ≤ N}`. -/
def charRow (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (N : ℕ) : ℕ → ℝ := dampedSignWeight (charCut χ N) ε

theorem completedValue_mul_self (χ : MulChar (ZMod q) ℤ) (e : ℕ) :
    completedValue χ e * completedValue χ e = 1 := by
  have h := abs_completedValue χ e
  rw [← abs_mul_abs_self, h, one_mul]

omit [NeZero q] in
theorem completedValue_mul_dampedSignWeight (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (e : ℕ) :
    completedValue χ e * dampedSignWeight (charSign χ) ε e = dampedSignWeight (charUnit χ) ε e := by
  unfold completedValue dampedSignWeight charUnit
  split_ifs with h
  · rw [h]; ring
  · ring

/-- **The parity twin at horizon `N`**: Selberg coordinates `χ̂(e) Y_N(e)`. -/
def charTwinRow (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (N : ℕ) : ℕ → ℝ :=
  scaledSelbergRow N (charRow χ ε N) (completedValue χ)

/-! ### Identical complete-period data -/

theorem sq_selbergMultiplesCoord_charTwinRow (χ : MulChar (ZMod q) ℤ) (ε : ℝ) {N e : ℕ}
    (he : e ∈ Icc 1 N) :
    selbergMultiplesCoord N (charTwinRow χ ε N) e ^ 2 =
      selbergMultiplesCoord N (charRow χ ε N) e ^ 2 := by
  rw [charTwinRow, selbergMultiplesCoord_scaledSelbergRow _ _ he, mul_pow, sq (completedValue χ e),
    completedValue_mul_self, one_mul]

theorem translatedMoment_two_charTwinRow (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (N : ℕ) (v : Fin 2 → ℕ) :
    SieveMoments.translatedMoment N (charTwinRow χ ε N) v =
      SieveMoments.translatedMoment N (charRow χ ε N) v :=
  translatedMoment_two_scaled_eq N _ (completedValue_mul_self χ) v

omit [NeZero q] in
/-- `Y_N(e) = (c_χ(e)/e) L_{N/e}`, `L_X = Σ_{k ≤ X} χ(k) k^{-1-ε}`. -/
theorem selbergMultiplesCoord_charRow (χ : MulChar (ZMod q) ℤ) (ε : ℝ) {N e : ℕ} (he : 0 < e) :
    selbergMultiplesCoord N (charRow χ ε N) e =
      dampedSignWeight (charSign χ) ε e / e *
        ∑ k ∈ Icc 1 (N / e), dampedSignWeight (charSign χ) ε k / k := by
  unfold selbergMultiplesCoord
  rw [RHTower.sum_Icc_filter_dvd_reindex e N he, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hek : e * k ≤ N := by
    have := (mem_Icc.mp hk).2
    calc e * k ≤ e * (N / e) := Nat.mul_le_mul_left e this
      _ ≤ N := Nat.mul_div_le N e
  have hrow : charRow χ ε N (e * k) = dampedSignWeight (charSign χ) ε (e * k) := by
    simp [charRow, dampedSignWeight, charCut, hek]
  rw [hrow, dampedSignWeight_mul_div (charSign_mul χ)]

omit [NeZero q] in
theorem tsum_charRow_div (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (N : ℕ) :
    ∑' d : ℕ, charRow χ ε N d / d = selbergMultiplesCoord N (charRow χ ε N) 1 := by
  rw [tsum_eq_sum (s := Icc 1 N) fun d hd => ?_]
  · unfold selbergMultiplesCoord
    congr 1
    ext d; simp
  · rw [mem_Icc, not_and_or] at hd
    rcases hd with hd | hd
    · have : d = 0 := by omega
      simp [this]
    · simp [charRow, dampedSignWeight, charCut, show ¬ d ≤ N by omega]

/-- **The character rows are uniformly paid.** -/
theorem horizonPronicEnergy_charRow_le {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε)
    (N T : ℕ) :
    horizonPronicEnergy N (charRow χ ε N) T ≤
      36 * (q : ℝ) ^ 2 * ∑' n : ℕ, (n : ℝ) ^ (2 * (1 / (2 + ε)) - 2) := by
  have h := weightPronicEnergy_dampedSign_le (Nat.cast_nonneg q) hε (abs_sum_range_charCut_le hχ N) T
  unfold horizonPronicEnergy
  rw [← tsum_charRow_div]
  exact h

/-! ### The cubic separation -/

/-- A non-principal real character is `−1` at some odd integer. -/
theorem exists_odd_charSign_eq_neg_one {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) :
    ∃ n : ℕ, Odd n ∧ charSign χ n = -1 := by
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hχ
  have hu : IsUnit (χ (a : ZMod q)) := (a.isUnit).map χ.toMonoidHom
  have hval : χ (a : ZMod q) = -1 := (Int.isUnit_iff.mp hu).resolve_left ha
  set n := (a : ZMod q).val
  have hn : charSign χ n = -1 := by simp only [charSign, n, ZMod.natCast_zmod_val, hval]; norm_num
  have hcop : Nat.Coprime n q := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact a.isUnit
  rcases Nat.even_or_odd n with hev | hodd
  · rcases Nat.even_or_odd q with hqe | hqo
    · exfalso
      have h2 : 2 ∣ Nat.gcd n q := Nat.dvd_gcd (even_iff_two_dvd.mp hev) (even_iff_two_dvd.mp hqe)
      rw [hcop] at h2; omega
    · refine ⟨q * 1 + n, ?_, by rw [charSign_mul_period_add, hn]⟩
      rw [mul_one]; exact hqo.add_even hev
  · exact ⟨n, hodd, hn⟩

/-! ### The twin rows converge to the signed positive twin -/

/-- `u(n) = 1_{(n,q)=1} n^{-1-ε}`. -/
private abbrev unitW (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (n : ℕ) : ℝ :=
  dampedSignWeight (charUnit χ) ε n / n

omit [NeZero q] in
private theorem unitW_mul (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (a b : ℕ) :
    unitW χ ε (a * b) = unitW χ ε a * unitW χ ε b :=
  dampedSignWeight_mul_div (charUnit_mul χ) a b

private theorem abs_unitW_le (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    |unitW χ ε n| ≤ (n : ℝ) ^ (-(1 + ε)) := by
  rw [unitW, dampedSignWeight_div hε, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    abs_of_nonneg (charUnit_nonneg χ n)]
  have h1 : charUnit χ n ≤ 1 := by
    have h := abs_charSign_le χ n
    unfold charUnit; nlinarith [abs_nonneg (charSign χ n), sq_abs (charSign χ n)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg n) _) h1

/-- `(Σ_m μ(m) u(m)) O_χ = 1`: Möbius inversion of the unit mass. -/
theorem tsum_moebius_mul_unitW_mul_charUnitMass (χ : MulChar (ZMod q) ℤ) {ε : ℝ} (hε : 0 < ε) :
    (∑' m : ℕ, moebiusReal m * unitW χ ε m) * charUnitMass χ ε = 1 := by
  have hclass : DampedClass 1 ε (dampedSignWeight (charUnit χ) ε) := fun d => by
    rw [dampedSignWeight, abs_mul, abs_of_nonneg (charUnit_nonneg χ d),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), one_mul]
    have h1 : charUnit χ d ≤ 1 := by
      have h := abs_charSign_le χ d
      unfold charUnit; nlinarith [abs_nonneg (charSign χ d), sq_abs (charSign χ d)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) h1
  have h := hasSum_moebius_mul_weightRamanujanCoeff hε hclass (d := 1) one_pos
  have hW : ∀ m, weightRamanujanCoeff (dampedSignWeight (charUnit χ) ε) (1 * m) =
      unitW χ ε m * charUnitMass χ ε := fun m => by
    rw [one_mul, weightRamanujanCoeff]
    simp_rw [dampedSignWeight_mul_div (charUnit_mul χ) m]
    rw [tsum_mul_left]; rfl
  simp_rw [hW] at h
  have h1 : dampedSignWeight (charUnit χ) ε 1 / ((1 : ℕ) : ℝ) = 1 := by
    simp [dampedSignWeight, charUnit, charSign_one]
  rw [h1] at h
  rw [← h.tsum_eq, ← tsum_mul_right]
  exact tsum_congr fun m => by ring

omit [NeZero q] in
/-- The twin row in closed form: `c'_N(d) = d Σ_{m ≤ N/d} μ(m) u(dm) L_{N/(dm)}`. -/
private theorem charTwinRow_eq (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (N : ℕ) {d : ℕ} (hd : 0 < d) :
    charTwinRow χ ε N d = (d : ℝ) * ∑ m ∈ Icc 1 (N / d), moebiusReal m *
      (unitW χ ε (d * m) * ∑ k ∈ Icc 1 (N / d / m), dampedSignWeight (charSign χ) ε k / k) := by
  unfold charTwinRow scaledSelbergRow RHTower.pmRamanujanResidueCoeff
  congr 1
  refine sum_congr rfl fun m hm => ?_
  dsimp only
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  rw [selbergMultiplesCoord_charRow χ ε (Nat.mul_pos hd hm0), Nat.div_div_eq_div_mul,
    ← mul_assoc (completedValue χ (d * m)), ← mul_div_assoc, completedValue_mul_dampedSignWeight]
  rfl

/-- The signed positive twin `(L/O) 1_{(d,q)=1} d^{-ε}`. -/
def charSignedTwin (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (d : ℕ) : ℝ :=
  charDampedMass χ ε / charUnitMass χ ε * dampedSignWeight (charUnit χ) ε d

/-- **The twin rows converge to the signed positive twin**, divisor by divisor. -/
theorem tendsto_charTwinRow {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    Tendsto (fun N => charTwinRow χ ε N d) atTop (𝓝 (charSignedTwin χ ε d)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : ∀ N, charTwinRow χ ε N 0 = 0 := fun N => by
      simp [charTwinRow, scaledSelbergRow, RHTower.pmRamanujanResidueCoeff]
    simp only [h0]
    have : charSignedTwin χ ε 0 = 0 := by
      simp [charSignedTwin, dampedSignWeight, Real.zero_rpow (show -ε ≠ 0 by linarith)]
    rw [this]
    exact tendsto_const_nhds
  set L := charDampedMass χ ε
  set Z := ∑' k : ℕ, (k : ℝ) ^ (-(1 + ε))
  have hZs : Summable (fun k : ℕ => (k : ℝ) ^ (-(1 + ε))) := Real.summable_nat_rpow.mpr (by linarith)
  have hLsum : HasSum (fun k : ℕ => dampedSignWeight (charSign χ) ε k / k) L :=
    (summable_dampedSignWeight_div (Nat.cast_nonneg q) hε (abs_sum_range_charSign_le hχ)).hasSum
  have hLX : Tendsto (fun X : ℕ => ∑ k ∈ Icc 1 X, dampedSignWeight (charSign χ) ε k / k) atTop
      (𝓝 L) := by
    refine (hLsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun X => ?_
    simp only [Function.comp_apply]
    rw [dampedSign_sum_range_succ_eq_add_Icc]
    simp [dampedSignWeight]
  have hLbound : ∀ X : ℕ, |∑ k ∈ Icc 1 X, dampedSignWeight (charSign χ) ε k / k| ≤ Z := fun X => by
    calc |∑ k ∈ Icc 1 X, dampedSignWeight (charSign χ) ε k / k| ≤
          ∑ k ∈ Icc 1 X, |dampedSignWeight (charSign χ) ε k / k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 X, (k : ℝ) ^ (-(1 + ε)) := sum_le_sum fun k _ => by
          rw [dampedSignWeight_div hε, abs_mul,
            abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)]
          exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg k) _) (abs_charSign_le χ k)
      _ ≤ Z := hZs.sum_le_tsum _ fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  set F : ℕ → ℕ → ℝ := fun N m => if m ∈ Icc 1 (N / d) then moebiusReal m *
      (unitW χ ε (d * m) * ∑ k ∈ Icc 1 (N / d / m), dampedSignWeight (charSign χ) ε k / k) else 0
  have hFsum : ∀ N, charTwinRow χ ε N d = (d : ℝ) * ∑' m, F N m := by
    intro N
    rw [charTwinRow_eq χ ε N hd, tsum_eq_sum (s := Icc 1 (N / d)) fun m hm => by
      simp only [F, if_neg hm]]
    congr 1
    exact sum_congr rfl fun m hm => by simp only [F, if_pos hm]
  have hμ1 : ∀ m : ℕ, |moebiusReal m| ≤ 1 := fun m => by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or m with h | h | h <;> simp [h]
  have hbound : ∀ N m, |F N m| ≤ Z * (m : ℝ) ^ (-(1 + ε)) := by
    intro N m
    simp only [F]
    split_ifs with hm
    · have hm1 := (mem_Icc.mp hm)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1.1
      have hu : |unitW χ ε (d * m)| ≤ (m : ℝ) ^ (-(1 + ε)) := by
        refine (abs_unitW_le χ hε _).trans ?_
        push_cast
        exact Real.rpow_le_rpow_of_nonpos hm0 (by nlinarith) (by linarith)
      rw [abs_mul, abs_mul]
      calc |moebiusReal m| * (|unitW χ ε (d * m)| *
            |∑ k ∈ Icc 1 (N / d / m), dampedSignWeight (charSign χ) ε k / k|)
          ≤ 1 * ((m : ℝ) ^ (-(1 + ε)) * Z) :=
            mul_le_mul (hμ1 m) (mul_le_mul hu (hLbound _) (abs_nonneg _)
              (Real.rpow_nonneg (Nat.cast_nonneg m) _)) (by positivity) (by norm_num)
        _ = Z * (m : ℝ) ^ (-(1 + ε)) := by ring
    · simp only [abs_zero]
      exact mul_nonneg (tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _)
        (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  have hlim : ∀ m, Tendsto (fun N => F N m) atTop (𝓝 (moebiusReal m * (unitW χ ε (d * m) * L))) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, moebiusReal]
    have hev : ∀ᶠ N in atTop, m ∈ Icc 1 (N / d) := by
      filter_upwards [eventually_ge_atTop (d * m)] with N hN
      exact mem_Icc.mpr ⟨hm, (Nat.le_div_iff_mul_le hd).mpr (by linarith [mul_comm d m])⟩
    have hdiv : Tendsto (fun N => N / d / m) atTop atTop :=
      (Nat.tendsto_div_const_atTop hm.ne').comp (Nat.tendsto_div_const_atTop hd.ne')
    have hmain := ((hLX.comp hdiv).const_mul (unitW χ ε (d * m))).const_mul (moebiusReal m)
    refine hmain.congr' ?_
    filter_upwards [hev] with N hN
    simp only [F, if_pos hN, Function.comp_apply]
  have hdom := tendsto_tsum_of_dominated_convergence
    (bound := fun m : ℕ => Z * ((m : ℕ) : ℝ) ^ (-(1 + ε))) (hZs.mul_left Z) hlim
    (Eventually.of_forall fun N m => by simpa [Real.norm_eq_abs] using hbound N m)
  have hlimit : (d : ℝ) * ∑' m, moebiusReal m * (unitW χ ε (d * m) * L) = charSignedTwin χ ε d := by
    have hO := (charUnitMass_pos χ hε).ne'
    have hinv := tsum_moebius_mul_unitW_mul_charUnitMass χ hε
    have hrw : ∀ m, moebiusReal m * (unitW χ ε (d * m) * L) =
        (unitW χ ε d * L) * (moebiusReal m * unitW χ ε m) := fun m => by rw [unitW_mul]; ring
    simp_rw [hrw]
    rw [tsum_mul_left]
    have hT : ∑' m : ℕ, moebiusReal m * unitW χ ε m = 1 / charUnitMass χ ε := by
      rw [eq_div_iff hO]; exact hinv
    rw [hT, charSignedTwin]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [unitW]
    field_simp
    rfl
  rw [← hlimit]
  refine (hdom.const_mul (d : ℝ)).congr fun N => ?_
  rw [hFsum]

theorem tendsto_selbergMultiplesCoord_one_charTwinRow {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => selbergMultiplesCoord N (charTwinRow χ ε N) 1) atTop (𝓝 (charDampedMass χ ε)) := by
  have hLsum : HasSum (fun k : ℕ => dampedSignWeight (charSign χ) ε k / k) (charDampedMass χ ε) :=
    (summable_dampedSignWeight_div (Nat.cast_nonneg q) hε (abs_sum_range_charSign_le hχ)).hasSum
  have hLX := hLsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine (hLX.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Function.comp_apply]
  rw [charTwinRow, selbergMultiplesCoord_scaledSelbergRow _ _ (mem_Icc.mpr ⟨le_refl 1, hN⟩),
    selbergMultiplesCoord_charRow χ ε one_pos, dampedSign_sum_range_succ_eq_add_Icc]
  have hs1 : completedValue χ 1 = 1 := by simp [completedValue, charSign_one]
  simp [hs1, charSign_one, dampedSignWeight]

/-- **The twin rows are unpaid.** -/
theorem eventually_lt_horizonPronicEnergy_charTwinRow {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (C : ℝ) :
    ∀ᶠ N in atTop, ∃ T, C < horizonPronicEnergy N (charTwinRow χ ε N) T := by
  have hL := charDampedMass_ne_zero (χ := χ) hε
  -- the signed twin has the receiver of the positive twin
  set t : ℝ := charDampedMass χ ε / |charDampedMass χ ε|
  have ht : t ^ 2 = 1 := by
    simp only [t]; rw [div_pow, sq_abs, div_self (pow_ne_zero 2 hL)]
  have hsigned : ∀ T, weightPronicEnergy (charSignedTwin χ ε) (charDampedMass χ ε) T =
      weightPronicEnergy (charTwinWeight χ ε) |charDampedMass χ ε| T := fun T => by
    have hfun : charSignedTwin χ ε = fun d => t * charTwinWeight χ ε d := funext fun d => by
      simp only [charSignedTwin, charTwinWeight, t]
      field_simp
    have hmean : charDampedMass χ ε = t * |charDampedMass χ ε| := by
      simp only [t]; field_simp
    rw [hfun]
    calc weightPronicEnergy (fun d => t * charTwinWeight χ ε d) (charDampedMass χ ε) T
        = weightPronicEnergy (fun d => t * charTwinWeight χ ε d) (t * |charDampedMass χ ε|) T := by
          rw [← hmean]
      _ = _ := by rw [weightPronicEnergy_smul, ht, one_mul]
  obtain ⟨T, hT⟩ := ((char_parityPair hχ hε hε2).2.2.2.eventually_gt_atTop C).exists
  have hconv := tendsto_weightPronicEnergy_of_pointwise (tendsto_charTwinRow hχ hε)
    (tendsto_selbergMultiplesCoord_one_charTwinRow hχ hε) T
  rw [hsigned] at hconv
  filter_upwards [hconv.eventually (lt_mem_nhds hT)] with N hN
  exact ⟨T, hN⟩

/-- **The cubic moment separates the rows** at all large horizons. -/
theorem eventually_exists_translatedMoment_three_charTwinRow_ne {χ : MulChar (ZMod q) ℤ}
    (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (charTwinRow χ ε N) v ≠
      SieveMoments.translatedMoment N (charRow χ ε N) v := by
  obtain ⟨n₀, hodd, hneg⟩ := exists_odd_charSign_eq_neg_one hχ
  have hn₀ : 0 < n₀ := hodd.pos
  have hL := charDampedMass_ne_zero (χ := χ) hε
  have hLsum : HasSum (fun k : ℕ => dampedSignWeight (charSign χ) ε k / k) (charDampedMass χ ε) :=
    (summable_dampedSignWeight_div (Nat.cast_nonneg q) hε (abs_sum_range_charSign_le hχ)).hasSum
  have hLX : Tendsto (fun X : ℕ => ∑ k ∈ Icc 1 X, dampedSignWeight (charSign χ) ε k / k) atTop
      (𝓝 (charDampedMass χ ε)) := by
    refine (hLsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun X => ?_
    simp only [Function.comp_apply]
    rw [dampedSign_sum_range_succ_eq_add_Icc]
    simp [dampedSignWeight]
  have hev := (hLX.comp (Nat.tendsto_div_const_atTop hn₀.ne')).eventually_ne hL
  filter_upwards [hev, eventually_ge_atTop n₀] with N hN hNn
  by_contra hall
  push Not at hall
  have hY : selbergMultiplesCoord N (charRow χ ε N) n₀ ≠ 0 := by
    rw [selbergMultiplesCoord_charRow χ ε hn₀]
    have hc : dampedSignWeight (charSign χ) ε n₀ / n₀ ≠ 0 := by
      have : (n₀ : ℝ) ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos (by exact_mod_cast hn₀) _).ne'
      simp [dampedSignWeight, hneg, this, hn₀.ne']
    exact mul_ne_zero hc hN
  have h3 := sign_cube_eq_one_of_translatedMoment_three (mem_Icc.mpr ⟨hn₀, hNn⟩) hodd
    (charRow χ ε N) (completedValue χ) hY hall
  have hσ : completedValue χ n₀ = -1 := by simp [completedValue, hneg]
  rw [hσ] at h3
  norm_num at h3

/-- **The parity rows of every real character.** For every real non-principal `χ` and every
`0 < ε ≤ 1/2`: at every horizon the row and its twin have Selberg coordinates equal up to sign and
identical two-point translated moments; at all large horizons a cubic translated moment separates
them; the character rows have uniformly bounded pronic discrepancy energy, the twins' tends to
infinity. -/
theorem char_parityRows {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    (∀ N e, e ∈ Icc 1 N → selbergMultiplesCoord N (charTwinRow χ ε N) e ^ 2 =
        selbergMultiplesCoord N (charRow χ ε N) e ^ 2) ∧
    (∀ N (v : Fin 2 → ℕ), SieveMoments.translatedMoment N (charTwinRow χ ε N) v =
        SieveMoments.translatedMoment N (charRow χ ε N) v) ∧
    (∀ᶠ N in atTop, ∃ v : Fin 3 → ℕ, SieveMoments.translatedMoment N (charTwinRow χ ε N) v ≠
        SieveMoments.translatedMoment N (charRow χ ε N) v) ∧
    (∃ C : ℝ, ∀ N T, horizonPronicEnergy N (charRow χ ε N) T ≤ C) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T, C < horizonPronicEnergy N (charTwinRow χ ε N) T) :=
  ⟨fun _ _ he => sq_selbergMultiplesCoord_charTwinRow χ ε he,
    translatedMoment_two_charTwinRow χ ε,
    eventually_exists_translatedMoment_three_charTwinRow_ne hχ hε,
    ⟨_, horizonPronicEnergy_charRow_le hχ hε⟩,
    eventually_lt_horizonPronicEnergy_charTwinRow hχ hε hε2⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
