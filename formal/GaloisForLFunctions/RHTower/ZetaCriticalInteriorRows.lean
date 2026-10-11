import GaloisForLFunctions.RHTower.ZetaCriticalRowNumerics
import GaloisForLFunctions.RHTower.ZetaCriticalCountControl
import GaloisForLFunctions.RHTower.ZetaCriticalPairDecomposition
import GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalWindow

/-!
# Interior rows at the critical scale

Let `T` be large, `L = log T`, `Y = 3T^{1/2}`, `x = T^{1/20}`, `τ₁ = 10¹³/L`, `τ₂ = 32 · 10¹³/L`,
`Θ = (L/2 − 1)/80`, and let `I` be the ordered indices with `Y ≤ γ_n ≤ T`. Assume:

* the zeros are `C/L`-rigid on `[T^{1/2}, T³]` with `C = 10⁶⁰`;
* the explicit-formula bound for the narrow mass holds at every height `p ∈ [Y − 1, T + 1]`.

* `norm_critRow_le_of_goodHeight`: at heights `t ∈ [Y + 1/2, T − 1/2]` outside the bad set (the
  Selberg polynomial is `≤ Θ` at all 13 grid points and both scales), every row `Ψ_n` with
  `|γ_n − t| ≤ τ₁` has `‖Ψ_n‖ ≤ 10⁻⁴`.
* `sum_norm_critRow_le_badHeight`: at every such height, the rows with `|γ_n − t| ≤ τ₁` sum to at
  most `96(10²⁶ + τ₁²‖D(½ + τ₁ + it)‖²)`.
* `sum_norm_critRow_interior_le`: the box partition then gives
  `Σ_{Y + 1 ≤ γ_n ≤ T − 1} ‖Ψ_n‖ ≤ 10⁻⁴ #I + TL/20000`.
* `sum_norm_critRow_interior_le_of_rigidOff`: if rigidity is only known at heights outside a set
  `N` of measure `≤ ν`, the same bound holds up to an extra `48 · 10¹³ νL`.
-/

noncomputable section

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry (lorentzF card_le_two_mul_sum_lorentz box_partition_sum_le)

namespace RHTower

/-- `T^{1/2}` is huge when `log T ≥ 10²⁵`. -/
theorem crit_rpow_half_ge {T : ℝ} (hT1 : 1 ≤ T) (hL : 10 ^ 25 ≤ Real.log T) :
    10 ^ 24 ≤ T ^ (1 / 2 : ℝ) := by
  rw [Real.rpow_def_of_pos (by linarith)]
  have := Real.add_one_le_exp (Real.log T * (1 / 2))
  nlinarith

/-- `log(t/2π) ≥ L/2 − 1` for `t ≥ 3T^{1/2}`. -/
theorem crit_log_ge {T t : ℝ} (hT1 : 1 ≤ T) (ht : 3 * T ^ (1 / 2 : ℝ) ≤ t) :
    Real.log T / 2 - 1 ≤ Real.log (t / (2 * Real.pi)) := by
  have hs : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have he := Real.exp_one_gt_d9
  have h1 : Real.exp (Real.log T / 2 - 1) ≤ t / (2 * Real.pi) := by
    have e : Real.exp (Real.log T / 2 - 1) = T ^ (1 / 2 : ℝ) / Real.exp 1 := by
      rw [Real.exp_sub, show Real.log T / 2 = Real.log T * (1 / 2) by ring,
        ← Real.rpow_def_of_pos (by linarith)]
    rw [e, div_le_div_iff₀ (Real.exp_pos 1) (by positivity)]
    have h3 : 2 * Real.pi ≤ 3 * Real.exp 1 := by nlinarith
    have h4 : T ^ (1 / 2 : ℝ) * (2 * Real.pi) ≤ T ^ (1 / 2 : ℝ) * (3 * Real.exp 1) :=
      mul_le_mul_of_nonneg_left h3 hs.le
    have h5 : 3 * T ^ (1 / 2 : ℝ) * Real.exp 1 ≤ t * Real.exp 1 :=
      mul_le_mul_of_nonneg_right ht (Real.exp_pos 1).le
    nlinarith
  calc Real.log T / 2 - 1 = Real.log (Real.exp (Real.log T / 2 - 1)) := (Real.log_exp _).symm
    _ ≤ Real.log (t / (2 * Real.pi)) := Real.log_le_log (Real.exp_pos _) h1

/-- `log(t/2π) ≤ L` for `0 < t ≤ T`. -/
theorem crit_log_le {T t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    Real.log (t / (2 * Real.pi)) ≤ Real.log T := by
  apply Real.log_le_log (by positivity)
  have := Real.pi_gt_three
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Nearby heights have nearby logarithms. -/
theorem abs_log_div_sub_le {p t : ℝ} (ht : 2 ≤ t) (hp : |p - t| ≤ 1) :
    |Real.log (p / (2 * Real.pi)) - Real.log (t / (2 * Real.pi))| ≤ 1 := by
  rw [abs_le] at hp
  have hp0 : 0 < p := by linarith
  have ht0 : 0 < t := by linarith
  have hπ := Real.pi_pos
  have e : Real.log (p / (2 * Real.pi)) - Real.log (t / (2 * Real.pi)) = Real.log (p / t) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_div (by positivity)
      (by positivity), Real.log_div (by positivity) (by positivity)]; ring
  rw [e, abs_le]
  constructor
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < t / p by positivity)
    rw [Real.log_div ht0.ne' hp0.ne'] at h1
    rw [Real.log_div hp0.ne' ht0.ne']
    have : t / p - 1 ≤ 1 := by rw [div_sub_one hp0.ne', div_le_one hp0]; linarith
    linarith
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < p / t by positivity)
    have : p / t - 1 ≤ 1 := by rw [div_sub_one ht0.ne', div_le_one ht0]; linarith
    linarith

/-- `κ(τ) ≤ 1/160` at the critical scales. -/
theorem crit_kappa_le {L B lx : ℝ} (hL : 0 < L) (hlx : lx = L / 20) (hB : 10 ^ 13 ≤ B) :
    2 * Real.exp (-(B / L * lx)) / (lx * (B / L)) ≤ 1 / 160 := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have e : B / L * lx = B / 20 := by rw [hlx]; field_simp
  have e' : lx * (B / L) = B / 20 := by rw [hlx]; field_simp
  rw [e, e']
  have h1 : Real.exp (-(B / 20)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [div_le_iff₀ (by positivity)]
  nlinarith


/-- Count control at one grid point from the explicit-formula bound. -/
theorem countControl_critical_point {L x t p τ B : ℝ} (hL : 10 ^ 25 ≤ L)
    (hlx : Real.log x = L / 20) (hB : 10 ^ 13 ≤ B) (hτ : τ = B / L) (ht : 2 ≤ t)
    (hp : |p - t| ≤ 1) (hℓ1 : L / 2 - 1 ≤ Real.log (t / (2 * Real.pi)))
    (hV : |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
      τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ +
        2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ p + 2 * τ +
        4 * τ * lorentzMassW (p / 2) p)
    (hW : lorentzMassW (p / 2) p ≤ 1 / 4)
    (hD : ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ ≤ (L / 2 - 1) / 80) :
    CountControl τ (Real.log (t / (2 * Real.pi))) (1 / 20) p := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hτ0 : 0 < τ := by rw [hτ]; exact div_pos (lt_of_lt_of_le (by norm_num) hB) hL0
  have hκ : 2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) ≤ 1 / 20 / 8 := by
    rw [hτ]; exact (crit_kappa_le hL0 hlx hB).trans (by norm_num)
  refine countControl_of_bound (Θ := (L / 2 - 1) / 80) hτ0 (by norm_num) (by norm_num) hκ
    (by linarith) hW (abs_log_div_sub_le ht hp) (by linarith) ?_
  refine hV.trans ?_
  have : τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ ≤ τ * ((L / 2 - 1) / 80) :=
    mul_le_mul_of_nonneg_left hD hτ0.le
  linarith

/-- **Good heights give small rows.** -/
theorem norm_critRow_le_of_goodHeight {T x t : ℝ} {n : ℕ} (hT1 : 1 ≤ T)
    (hL : 10 ^ 25 ≤ Real.log T) (hlx : Real.log x = Real.log T / 20)
    (hA : 3 * T ^ (1 / 2 : ℝ) + 1 / 2 ≤ t) (hBt : t ≤ T - 1 / 2)
    (hV : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → p ≤ T + 1 → ∀ τ, 0 < τ → τ ≤ 1 / 2 →
      |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
        τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ +
          2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ p + 2 * τ +
          4 * τ * lorentzMassW (p / 2) p)
    (hW : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4)
    (hrigt : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * (32 * 10 ^ 13 / Real.log T) →
      RigidAt (10 ^ 60 / Real.log T) k)
    (hgood : t ∉ criticalBadSet x (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
      ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2))
    (hn : |xiOrderedPositiveOrdinate n - t| ≤ 10 ^ 13 / Real.log T) :
    ‖critRow (Real.log T / 8) (Real.log T / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤
      1 / 10000 := by
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hs := crit_rpow_half_ge hT1 hL
  have hτ₂s : 32 * 10 ^ 13 / L ≤ 1 / 10 ^ 10 := by
    rw [div_le_iff₀ hL0]; nlinarith
  have hτ₁₂ : (10 : ℝ) ^ 13 / L ≤ 32 * 10 ^ 13 / L := by gcongr; norm_num
  have ht2 : 2 ≤ t := by nlinarith
  have hℓ1 := crit_log_ge hT1 (show 3 * T ^ (1 / 2 : ℝ) ≤ t by linarith)
  have hℓ2 := crit_log_le (by linarith) (show t ≤ T by linarith)
  rw [← hLdef] at hℓ1 hℓ2
  set u := Real.log (t / (2 * Real.pi)) / L with hu
  have huL : u * L = Real.log (t / (2 * Real.pi)) := by rw [hu]; field_simp
  have hu1 : 9 / 20 ≤ u := by
    rw [hu, le_div_iff₀ hL0]; nlinarith
  have hu2 : u ≤ 1 := by rw [hu, div_le_one hL0]; exact hℓ2
  -- the grid
  have hgrid : ∀ j : ℤ, |j| ≤ 6 → |t + 2 * j * (32 * 10 ^ 13 / L) - t| ≤ 1 := by
    intro j hj
    have hj' : |(j : ℝ)| ≤ 6 := by exact_mod_cast hj
    rw [show t + 2 * j * (32 * 10 ^ 13 / L) - t = 2 * j * (32 * 10 ^ 13 / L) by ring, abs_mul,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (div_pos (by norm_num) hL0)]
    have : 2 * |(j : ℝ)| * (32 * 10 ^ 13 / L) ≤ 2 * 6 * (1 / 10 ^ 10) := by gcongr
    linarith
  have hD : ∀ j : ℤ, |j| ≤ 6 →
      ‖selbergVonMangoldtPoly x (narrowPoint (10 ^ 13 / L) (t + 2 * j * (32 * 10 ^ 13 / L)))‖ ≤
        (L / 2 - 1) / 80 ∧
      ‖selbergVonMangoldtPoly x (narrowPoint (32 * 10 ^ 13 / L) (t + 2 * j * (32 * 10 ^ 13 / L)))‖
        ≤ (L / 2 - 1) / 80 := by
    intro j hj
    by_contra hcon
    rw [not_and_or] at hcon
    push Not at hcon
    exact hgood ⟨⟨hA, hBt⟩, j, hj, hcon⟩
  have hC : ∀ j : ℤ, |j| ≤ 6 →
      CountControl (10 ^ 13 / L) (u * L) (1 / 20) (t + 2 * j * (32 * 10 ^ 13 / L)) ∧
        CountControl (32 * 10 ^ 13 / L) (u * L) (1 / 20) (t + 2 * j * (32 * 10 ^ 13 / L)) := by
    intro j hj
    have hp := hgrid j hj
    rw [abs_le] at hp
    have hp1 : 3 * T ^ (1 / 2 : ℝ) - 1 ≤ t + 2 * j * (32 * 10 ^ 13 / L) := by linarith
    have hp2 : t + 2 * j * (32 * 10 ^ 13 / L) ≤ T + 1 := by linarith
    rw [huL]
    refine ⟨countControl_critical_point hL hlx le_rfl rfl ht2 (hgrid j hj) hℓ1
      (hV _ hp1 hp2 _ (by positivity) (by linarith)) (hW _ hp1) (hD j hj).1,
      countControl_critical_point hL hlx (by norm_num) rfl ht2 (hgrid j hj) hℓ1
      (hV _ hp1 hp2 _ (by positivity) (by linarith)) (hW _ hp1) (hD j hj).2⟩
  -- the window lies in the rigid bulk
  have hsT : T ^ (1 / 2 : ℝ) ≤ T := by
    calc T ^ (1 / 2 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one T
  have hT2 : 2 ≤ T := by nlinarith
  have hB : ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * (32 * 10 ^ 13 / L) →
      k ∈ bulkIndices (3 * T ^ (1 / 2 : ℝ)) T := by
    intro k hk
    rw [abs_le] at hk
    rw [mem_bulkIndices]
    constructor <;> nlinarith
  exact norm_critRow_le_critical hL hu1 hu2 (by nlinarith) hC hrigt hB hn


/-- **Rows at any height sum to a controlled amount.** -/
theorem sum_norm_critRow_le_badHeight {T x t : ℝ} (hT1 : 1 ≤ T)
    (hL : 10 ^ 25 ≤ Real.log T) (hlx : Real.log x = Real.log T / 20)
    (hA : 3 * T ^ (1 / 2 : ℝ) + 1 / 2 ≤ t) (hBt : t ≤ T - 1 / 2)
    (hV : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → p ≤ T + 1 → ∀ τ, 0 < τ → τ ≤ 1 / 2 →
      |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
        τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ +
          2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ p + 2 * τ +
          4 * τ * lorentzMassW (p / 2) p)
    (hW : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4)
    (S : Finset ℕ) :
    ∑ n ∈ S.filter (fun n => |xiOrderedPositiveOrdinate n - t| ≤ 10 ^ 13 / Real.log T),
        ‖critRow (Real.log T / 8) (Real.log T / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤
      96 * 10 ^ 26 + 96 * (10 ^ 13 / Real.log T) ^ 2 *
        ‖selbergVonMangoldtPoly x (narrowPoint (10 ^ 13 / Real.log T) t)‖ ^ 2 := by
  classical
  set L := Real.log T with hLdef
  set τ₁ : ℝ := 10 ^ 13 / L with hτ₁
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁s : τ₁ ≤ 1 / 10 ^ 10 := by rw [hτ₁, div_le_iff₀ hL0]; nlinarith
  have hs := crit_rpow_half_ge hT1 hL
  have ht2 : 2 ≤ t := by nlinarith
  have hℓ2 := crit_log_le (by linarith) (show t ≤ T by linarith)
  rw [← hLdef] at hℓ2
  set M := narrowMass τ₁ t with hM
  have hM0 : 0 ≤ M := narrowMass_nonneg _ _
  have hV0 := hV t (by linarith) (by linarith) τ₁ hτ₁0 (by linarith)
  have hκ : 2 * Real.exp (-(τ₁ * Real.log x)) / (Real.log x * τ₁) ≤ 1 / 2 := by
    rw [hτ₁]; exact (crit_kappa_le hL0 hlx le_rfl).trans (by norm_num)
  set Dn := ‖selbergVonMangoldtPoly x (narrowPoint τ₁ t)‖ with hDn
  have hMle : M ≤ τ₁ * L + 6 * τ₁ + 2 * τ₁ * Dn :=
    narrowMass_le_of_bound hτ₁0 hκ (hW t (by linarith)) hℓ2 hV0
  have hτL : τ₁ * L = 10 ^ 13 := by rw [hτ₁]; field_simp
  have hMle' : M ≤ 2 * 10 ^ 13 + 2 * (τ₁ * Dn) := by nlinarith
  -- each row and the number of rows
  have hrow : ∀ n ∈ S.filter (fun n => |xiOrderedPositiveOrdinate n - t| ≤ τ₁),
      ‖critRow (L / 8) (L / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤ 6 * M := by
    intro n hn
    rw [Finset.mem_filter] at hn
    refine norm_critRow_le_six_narrowMass (by positivity) ?_ (by linarith) _ hn.2
    rw [hτ₁, div_div_eq_mul_div, div_le_div_iff_of_pos_right hL0]; norm_num
  have hcard : ((S.filter (fun n => |xiOrderedPositiveOrdinate n - t| ≤ τ₁)).card : ℝ) ≤ 2 * M := by
    have h1 := card_le_two_mul_sum_lorentz hτ₁0 S xiOrderedPositiveOrdinate t
    have h2 := sum_lorentzF_ordinate_le_narrowMass hτ₁0 (by linarith) S t
    have e : S.filter (fun n => |xiOrderedPositiveOrdinate n - t| ≤ τ₁) =
        S.filter (fun n => |t - xiOrderedPositiveOrdinate n| ≤ τ₁) :=
      Finset.filter_congr fun n _ => by rw [abs_sub_comm]
    rw [e]; linarith
  calc ∑ n ∈ S.filter (fun n => |xiOrderedPositiveOrdinate n - t| ≤ τ₁),
        ‖critRow (L / 8) (L / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖
      ≤ ∑ _n ∈ S.filter (fun n => |xiOrderedPositiveOrdinate n - t| ≤ τ₁), 6 * M :=
        Finset.sum_le_sum hrow
    _ = ((S.filter (fun n => |xiOrderedPositiveOrdinate n - t| ≤ τ₁)).card : ℝ) * (6 * M) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * M * (6 * M) := by gcongr
    _ ≤ 96 * 10 ^ 26 + 96 * τ₁ ^ 2 * Dn ^ 2 := by
        have hb : 0 ≤ τ₁ * Dn := by positivity
        nlinarith [sq_nonneg (2 * 10 ^ 13 - 2 * (τ₁ * Dn))]


/-- The interior indices `Y + 1 ≤ γ_n ≤ T − 1`. -/
def interiorIndices (T : ℝ) : Finset ℕ :=
  (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T).filter fun n =>
    3 * T ^ (1 / 2 : ℝ) + 1 ≤ xiOrderedPositiveOrdinate n ∧ xiOrderedPositiveOrdinate n ≤ T - 1

/-- The bad integral at the critical constants: `≤ 10⁹ T + 96 · 10²⁶ ν` when the bad set is enlarged
by a set `N` of measure `≤ ν`. -/
theorem lintegral_criticalBad_le {T x ν : ℝ} {N : Set ℝ} (hT1 : 1 ≤ T)
    (hL : 10 ^ 25 ≤ Real.log T) (hx1 : 1 < x) (hν : 0 ≤ ν) (hN : volume N ≤ ENNReal.ofReal ν)
    (hlen : (T - 1 / 2) - (3 * T ^ (1 / 2 : ℝ) + 1 / 2) +
      8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) ≤ 2 * T) :
    ∫⁻ t, (criticalBadSet x (10 ^ 13 / Real.log T) (32 * 10 ^ 13 / Real.log T)
        ((Real.log T / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∪
          (Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∩ N)).indicator
        (fun t => ENNReal.ofReal (96 * 10 ^ 26 + 96 * (10 ^ 13 / Real.log T) ^ 2 *
          ‖selbergVonMangoldtPoly x (narrowPoint (10 ^ 13 / Real.log T) t)‖ ^ 2)) t ≤
      ENNReal.ofReal (10 ^ 9 * T + 96 * 10 ^ 26 * ν) := by
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  set τ₁ : ℝ := 10 ^ 13 / L with hτ₁
  set τ₂ : ℝ := 32 * 10 ^ 13 / L with hτ₂
  set Θ : ℝ := (L / 2 - 1) / 80 with hΘ
  set A := 3 * T ^ (1 / 2 : ℝ) + 1 / 2 with hA
  set B := T - 1 / 2 with hB
  set len := B - A + 8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) with hlendef
  have hs := crit_rpow_half_ge hT1 hL
  have hsT : T ^ (1 / 2 : ℝ) ≤ T := by
    calc T ^ (1 / 2 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one T
  have hsq : T ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) = T := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hAB : A ≤ B := by rw [hA, hB]; nlinarith
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁₂ : τ₁ ≤ τ₂ := by rw [hτ₁, hτ₂]; gcongr; norm_num
  have hτ₂1 : τ₂ ≤ 1 := by rw [hτ₂, div_le_one hL0]; linarith
  have hΘ0 : 0 < Θ := by rw [hΘ]; nlinarith
  have hΘL : L / 200 ≤ Θ := by rw [hΘ]; nlinarith
  have hbad := lintegral_bad_le (τ₁ := τ₁) (a := 96 * 10 ^ 26) (b := 96 * τ₁ ^ 2) hx1
    (by norm_num) (by positivity) hAB (criticalBadSet x τ₁ τ₂ Θ A B ∪ (Icc A B ∩ N))
    (union_subset inter_subset_left inter_subset_left)
  have hvol0 := volume_criticalBadSet_le hx1 hτ₁0 hτ₁₂ hτ₂1 hΘ0 hAB
  have hvol : volume (criticalBadSet x τ₁ τ₂ Θ A B ∪ (Icc A B ∩ N)) ≤
      ENNReal.ofReal (26 * (len * (5 / τ₁ ^ 2) / Θ ^ 2) + ν) := by
    refine (measure_union_le _ _).trans ?_
    rw [ENNReal.ofReal_add (by positivity) hν]
    exact add_le_add hvol0 ((measure_mono inter_subset_right).trans hN)
  have hms : ∫ t in A..B, ‖selbergVonMangoldtPoly x (narrowPoint τ₁ t)‖ ^ 2 ≤ len * (5 / τ₁ ^ 2) := by
    have := integral_normSq_selbergNarrow_shift_le hx1 hτ₁0 (by linarith) hAB 0
    simpa using this
  refine hbad.trans ?_
  have hlen0 : 0 ≤ len := by
    have h1 := Real.log_natCast_nonneg (selbergPolyLength x)
    have h2 : (0 : ℝ) ≤ selbergPolyLength x := Nat.cast_nonneg _
    rw [hlendef]; nlinarith
  have h1 : ENNReal.ofReal (96 * 10 ^ 26) * volume (criticalBadSet x τ₁ τ₂ Θ A B ∪ (Icc A B ∩ N)) ≤
      ENNReal.ofReal (96 * 10 ^ 26 * (26 * (len * (5 / τ₁ ^ 2) / Θ ^ 2) + ν)) := by
    rw [ENNReal.ofReal_mul (p := 96 * 10 ^ 26) (by norm_num)]
    gcongr
  have h2 : ENNReal.ofReal (96 * τ₁ ^ 2 * ∫ t in A..B,
      ‖selbergVonMangoldtPoly x (narrowPoint τ₁ t)‖ ^ 2) ≤
      ENNReal.ofReal (96 * τ₁ ^ 2 * (len * (5 / τ₁ ^ 2))) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hms (by positivity))
  refine (add_le_add h1 h2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- the arithmetic
  have hτΘ : 10 ^ 13 / 200 ≤ τ₁ * Θ := by
    have : τ₁ * (L / 200) = 10 ^ 13 / 200 := by rw [hτ₁]; field_simp
    rw [← this]; exact mul_le_mul_of_nonneg_left hΘL hτ₁0.le
  have e1 : 96 * 10 ^ 26 * (26 * (len * (5 / τ₁ ^ 2) / Θ ^ 2) + ν) =
      96 * 10 ^ 26 * 26 * 5 * len / (τ₁ * Θ) ^ 2 + 96 * 10 ^ 26 * ν := by field_simp
  have e2 : 96 * τ₁ ^ 2 * (len * (5 / τ₁ ^ 2)) = 480 * len := by field_simp; ring
  rw [e1, e2]
  have h3 : 96 * 10 ^ 26 * 26 * 5 * len / (τ₁ * Θ) ^ 2 ≤
      96 * 10 ^ 26 * 26 * 5 * len / (10 ^ 13 / 200) ^ 2 := by
    gcongr
  have h4 : 96 * 10 ^ 26 * 26 * 5 * len / (10 ^ 13 / 200) ^ 2 = 499200000 * len := by
    field_simp; ring
  have hlenT : len ≤ 2 * T := hlen
  nlinarith

/-- **The interior rows, with rigidity off an exceptional set `N`.** -/
theorem sum_norm_critRow_interior_le_of_rigidOff {T x ν : ℝ} {N : Set ℝ} (hT1 : 1 ≤ T)
    (hL : 10 ^ 25 ≤ Real.log T) (hx1 : 1 < x) (hlx : Real.log x = Real.log T / 20)
    (hV : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → p ≤ T + 1 → ∀ τ, 0 < τ → τ ≤ 1 / 2 →
      |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
        τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ +
          2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ p + 2 * τ +
          4 * τ * lorentzMassW (p / 2) p)
    (hW : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4)
    (hν : 0 ≤ ν) (hN : volume N ≤ ENNReal.ofReal ν)
    (hrigN : ∀ t ∈ Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2), t ∉ N →
      ∀ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * (32 * 10 ^ 13 / Real.log T) →
        RigidAt (10 ^ 60 / Real.log T) k)
    (hlen : (T - 1 / 2) - (3 * T ^ (1 / 2 : ℝ) + 1 / 2) +
      8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) ≤ 2 * T) :
    ∑ n ∈ interiorIndices T,
        ‖critRow (Real.log T / 8) (Real.log T / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤
      1 / 10000 * (interiorIndices T).card + T * Real.log T / 20000 +
        48 * 10 ^ 13 * ν * Real.log T := by
  classical
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  set τ₁ : ℝ := 10 ^ 13 / L with hτ₁
  have hτ₁0 : 0 < τ₁ := by positivity
  have hτ₁s : τ₁ ≤ 1 / 4 := by rw [hτ₁, div_le_iff₀ hL0]; nlinarith
  have hbox := box_partition_sum_le (S := interiorIndices T) (y := xiOrderedPositiveOrdinate)
    (ψ := fun n => ‖critRow (L / 8) (L / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖)
    (h := τ₁) (ε₁ := 1 / 10000) (I := 10 ^ 9 * T + 96 * 10 ^ 26 * ν) hτ₁0
    (fun n => norm_nonneg _) (by norm_num) (by positivity)
    (criticalBadSet x τ₁ (32 * 10 ^ 13 / L) ((L / 2 - 1) / 80) (3 * T ^ (1 / 2 : ℝ) + 1 / 2)
      (T - 1 / 2) ∪ (Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∩ N))
    (fun t => 96 * 10 ^ 26 + 96 * τ₁ ^ 2 * ‖selbergVonMangoldtPoly x (narrowPoint τ₁ t)‖ ^ 2)
    ?_ ?_ (lintegral_criticalBad_le hT1 hL hx1 hν hN hlen)
  · -- conclude
    have h1 : 2 * τ₁ * ∑ n ∈ interiorIndices T,
        ‖critRow (L / 8) (L / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤
        2 * τ₁ * (1 / 10000 * (interiorIndices T).card + T * L / 20000 +
          48 * 10 ^ 13 * ν * L) := by
      have e2 : 2 * τ₁ * (T * L / 20000) = 10 ^ 9 * T := by rw [hτ₁]; field_simp; ring
      have e3 : 2 * τ₁ * (48 * 10 ^ 13 * ν * L) = 96 * 10 ^ 26 * ν := by
        rw [hτ₁]; field_simp; ring
      nlinarith
    exact le_of_mul_le_mul_left h1 (by positivity)
  · -- good heights
    intro t ht n hn hnt
    have hn' := (Finset.mem_filter.mp hn).2
    rw [abs_le] at hnt
    have htA : 3 * T ^ (1 / 2 : ℝ) + 1 / 2 ≤ t := by linarith
    have htB : t ≤ T - 1 / 2 := by linarith
    have hn'' : |xiOrderedPositiveOrdinate n - t| ≤ 10 ^ 13 / L := by rw [abs_le]; exact hnt
    have htN : t ∉ N := fun h => ht (Or.inr ⟨⟨htA, htB⟩, h⟩)
    have htB' : t ∉ criticalBadSet x τ₁ (32 * 10 ^ 13 / L) ((L / 2 - 1) / 80)
        (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) := fun h => ht (Or.inl h)
    exact norm_critRow_le_of_goodHeight hT1 hL hlx htA htB hV hW (hrigN t ⟨htA, htB⟩ htN) htB' hn''
  · -- bad heights
    intro t ht
    have htI : t ∈ Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) := by
      rcases ht with h | h
      · exact h.1
      · exact h.1
    exact sum_norm_critRow_le_badHeight hT1 hL hlx htI.1 htI.2 hV hW _

/-- **The interior rows** under rigidity on the whole window. -/
theorem sum_norm_critRow_interior_le {T x : ℝ} (hT1 : 1 ≤ T) (hL : 10 ^ 25 ≤ Real.log T)
    (hx1 : 1 < x) (hlx : Real.log x = Real.log T / 20)
    (hV : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → p ≤ T + 1 → ∀ τ, 0 < τ → τ ≤ 1 / 2 →
      |narrowMass τ p - τ * Real.log (p / (2 * Real.pi)) / 2| ≤
        τ * ‖selbergVonMangoldtPoly x (narrowPoint τ p)‖ +
          2 * Real.exp (-(τ * Real.log x)) / (Real.log x * τ) * narrowMass τ p + 2 * τ +
          4 * τ * lorentzMassW (p / 2) p)
    (hW : ∀ p, 3 * T ^ (1 / 2 : ℝ) - 1 ≤ p → lorentzMassW (p / 2) p ≤ 1 / 4)
    (hrig : RigidWindow (10 ^ 60 / Real.log T) T)
    (hlen : (T - 1 / 2) - (3 * T ^ (1 / 2 : ℝ) + 1 / 2) +
      8 * selbergPolyLength x * (1 + Real.log (selbergPolyLength x)) ≤ 2 * T) :
    ∑ n ∈ interiorIndices T,
        ‖critRow (Real.log T / 8) (Real.log T / 16) (bulkIndices (3 * T ^ (1 / 2 : ℝ)) T) n‖ ≤
      1 / 10000 * (interiorIndices T).card + T * Real.log T / 20000 := by
  have h := sum_norm_critRow_interior_le_of_rigidOff (N := ∅) (ν := 0) hT1 hL hx1 hlx hV hW le_rfl
    (by simp) (fun t ht _ k hk => ?_) hlen
  · simpa using h
  set L := Real.log T with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hs := crit_rpow_half_ge hT1 hL
  have hsT : T ^ (1 / 2 : ℝ) ≤ T := by
    calc T ^ (1 / 2 : ℝ) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
      _ = T := Real.rpow_one T
  have hT2 : 2 ≤ T := by nlinarith
  have hT3 : T + 1 ≤ T ^ 3 := by
    have h1 : 4 ≤ T * T := by nlinarith
    nlinarith
  have hτ₂s : 32 * 10 ^ 13 / L ≤ 1 / 10 ^ 10 := by
    rw [div_le_iff₀ hL0]; nlinarith
  rw [abs_le] at hk
  exact hrig k (by nlinarith [ht.1]) (by nlinarith [ht.2])

end RHTower
