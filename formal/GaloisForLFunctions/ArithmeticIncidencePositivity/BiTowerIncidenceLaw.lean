import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerEulerEnvelope

/-!
# The bi-tower law: two spacings, with the product and ratio shifts as payers

The tower law bounds the charge of one geometric tower by its first-power autocorrelation. Two
towers are coupled: reading the `b`-train `G = Σ_{k ≤ N} w^k F(· + kb)` as the test and applying
the tower law to it at the spacing `a` gives a law for the whole lattice of lags `ma + jb`,
`m ≥ 1`, `j ∈ ℤ`. The autocorrelation of the train is the **train lag charge**

    A_G(s) = Σ_{j,k ≤ N} w^{j+k} A(s + (k − j) b),

a two-sided `b`-ladder of the lag `s`. At `z = p^{−1/2}`, `a = log p`, `w = q^{−1/2}`, `b = log q`
the lags are the integers `p^m q^{k−j}`, so the **product** shifts `log(p^m q^i)` and the **ratio**
shifts `log(p^m/q^i)` both occur, with the Euler weights of both primes. The law

    (1 − z²) Σ_{m ≥ 1} z^m A_G(ma) ≤ z² A_G(0) + z A_G(a)

says: the joint charge of the two towers together with all their mixed product and ratio shifts is
paid by the `b`-ladder at the two lags `0` and `a` — the first power of the first tower. The whole
coupling graph between two towers is therefore controlled by two ladder charges, and the discount
form shows that a ladder uncorrelated at the lag `a` pays only `z²/(1−z²)` of its mass.
-/

open MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-- A support bound gives compact support. -/
theorem hasCompactSupport_of_support_bound {B : ℝ} (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun x hx => hsupp x ?_
  rcases lt_or_ge x (-B) with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · have hxB : B < x := by
      by_contra hc
      exact hx (Set.mem_Icc.mpr ⟨h, not_lt.mp hc⟩)
    rw [abs_of_pos (by linarith)]
    exact hxB

/-! ### The train as a test -/

/-- The geometric train of a continuous test is continuous. -/
theorem continuous_geoTrain (hF : Continuous F) (w b : ℝ) (N : ℕ) :
    Continuous (geoTrain w b F N) := by
  show Continuous fun u => ∑ k ∈ Finset.range (N + 1), w ^ k * F (u + (k : ℝ) * b)
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.mul (hF.comp (continuous_id.add continuous_const))

/-- The `b`-train of a test supported in `[−B, B]` is supported in `[−(B + Nb), B + Nb]`. -/
theorem geoTrain_eq_zero_of_support {B w b : ℝ} (hB : 0 ≤ B) (hb : 0 ≤ b) (N : ℕ)
    (hsupp : ∀ x, B < |x| → F x = 0) {x : ℝ} (hx : B + (N : ℝ) * b < |x|) :
    geoTrain w b F N x = 0 := by
  show (∑ k ∈ Finset.range (N + 1), w ^ k * F (x + (k : ℝ) * b)) = 0
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkN : (k : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hNb : 0 ≤ (N : ℝ) * b := mul_nonneg (Nat.cast_nonneg N) hb
  have hkb : 0 ≤ (k : ℝ) * b := mul_nonneg hk0 hb
  have hkbN : (k : ℝ) * b ≤ (N : ℝ) * b := mul_le_mul_of_nonneg_right hkN hb
  have hgt : B < |x + (k : ℝ) * b| := by
    rcases lt_or_ge x 0 with h | h
    · rw [abs_of_neg h] at hx
      rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_nonneg h] at hx
      rw [abs_of_nonneg (by linarith)]
      linarith
  rw [hsupp _ hgt, mul_zero]

/-! ### The train lag charge -/

/-- The train lag charge `Σ_{j,k ≤ N} w^{j+k} A(s + (k − j) b)`: the two-sided `b`-ladder of the
lag `s` with geometric weights. It is the autocorrelation of the `b`-train at the lag `s`. -/
def trainLagCharge (w b : ℝ) (F : ℝ → ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    w ^ j * w ^ k * autoCorr F (s + ((k : ℝ) - (j : ℝ)) * b)

/-- The autocorrelation of the geometric train is the train lag charge. -/
theorem autoCorr_geoTrain_eq_trainLagCharge (hF : Continuous F) (hFc : HasCompactSupport F)
    (w b : ℝ) (N : ℕ) (s : ℝ) :
    autoCorr (geoTrain w b F N) s = trainLagCharge w b F N s := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  rw [autoCorr_eq_testPairing, geoTrain_shift w b F N s,
    show geoTrain w b F N
      = translateComb F (N + 1) (fun k => w ^ k) (fun k => (k : ℝ) * b) from rfl,
    testPairing_comb hFn]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [show (k : ℝ) * b + s - (j : ℝ) * b = s + ((k : ℝ) - (j : ℝ)) * b by ring]

/-! ### The bi-tower law -/

/-- **The bi-tower law.** For a continuous test supported in `[−B, B]`, two spacings `a, b > 0` and
ratios `z ∈ (0,1)`, `w` arbitrary,

    (1 − z²) Σ_{m ≥ 1} z^m A_G(ma) ≤ z² A_G(0) + z A_G(a),

where `A_G(s) = Σ_{j,k ≤ N} w^{j+k} A(s + (k − j)b)` is the `b`-ladder of the lag `s`. The left
side carries every mixed lag `ma + (k − j)b`: at `a = log p`, `b = log q` these are the products
`p^m q^i` and the ratios `p^m/q^i`. -/
theorem one_sub_sq_mul_tsum_trainLagCharge_le {B z w a b : ℝ} (hF : Continuous F) (hB : 0 ≤ B)
    (hsupp : ∀ x, B < |x| → F x = 0) (hz0 : 0 < z) (hz1 : z < 1) (ha : 0 < a) (hb : 0 < b)
    (N : ℕ) :
    (1 - z ^ 2) * (∑' m : ℕ, z ^ (m + 1) * trainLagCharge w b F N (((m : ℝ) + 1) * a))
      ≤ z ^ 2 * trainLagCharge w b F N 0 + z * trainLagCharge w b F N a := by
  have hFc : HasCompactSupport F := hasCompactSupport_of_support_bound hB hsupp
  have hGc : Continuous (geoTrain w b F N) := continuous_geoTrain hF w b N
  have hGsupp : ∀ x, B + (N : ℝ) * b < |x| → geoTrain w b F N x = 0 := fun x hx =>
    geoTrain_eq_zero_of_support hB hb.le N hsupp hx
  have hGB : 0 ≤ B + (N : ℝ) * b := by
    have : 0 ≤ (N : ℝ) * b := mul_nonneg (Nat.cast_nonneg N) hb.le
    linarith
  have key := one_sub_sq_mul_geoLagCharge_le hGc hGB hGsupp hz0 hz1 ha
  have hterm : (fun m : ℕ => z ^ (m + 1) * autoCorr (geoTrain w b F N) (((m : ℝ) + 1) * a))
      = fun m : ℕ => z ^ (m + 1) * trainLagCharge w b F N (((m : ℝ) + 1) * a) := by
    funext m
    rw [autoCorr_geoTrain_eq_trainLagCharge hF hFc]
  rw [geoLagCharge, hterm, autoCorr_geoTrain_eq_trainLagCharge hF hFc,
    autoCorr_geoTrain_eq_trainLagCharge hF hFc] at key
  exact key

/-- The discount form of the bi-tower law: the joint charge of the two towers is the Euler envelope
of the first tower applied to the ladder, discounted by the ladder's own first-power defect
`A_G(0) − A_G(a)`. A ladder uncorrelated at the lag `a` pays only `z²/(1 − z²)` of its mass. -/
theorem tsum_trainLagCharge_le_envelope_sub_discount {B z w a b : ℝ} (hF : Continuous F)
    (hB : 0 ≤ B) (hsupp : ∀ x, B < |x| → F x = 0) (hz0 : 0 < z) (hz1 : z < 1) (ha : 0 < a)
    (hb : 0 < b) (N : ℕ) :
    (∑' m : ℕ, z ^ (m + 1) * trainLagCharge w b F N (((m : ℝ) + 1) * a))
      ≤ z / (1 - z) * trainLagCharge w b F N 0
        - z / (1 - z ^ 2) * (trainLagCharge w b F N 0 - trainLagCharge w b F N a) := by
  have hFc : HasCompactSupport F := hasCompactSupport_of_support_bound hB hsupp
  have hGc : Continuous (geoTrain w b F N) := continuous_geoTrain hF w b N
  have hGsupp : ∀ x, B + (N : ℝ) * b < |x| → geoTrain w b F N x = 0 := fun x hx =>
    geoTrain_eq_zero_of_support hB hb.le N hsupp hx
  have hGB : 0 ≤ B + (N : ℝ) * b := by
    have : 0 ≤ (N : ℝ) * b := mul_nonneg (Nat.cast_nonneg N) hb.le
    linarith
  have key := geoLagCharge_le_envelope_sub_discount hGc hGB hGsupp hz0 hz1 ha
  have hterm : (fun m : ℕ => z ^ (m + 1) * autoCorr (geoTrain w b F N) (((m : ℝ) + 1) * a))
      = fun m : ℕ => z ^ (m + 1) * trainLagCharge w b F N (((m : ℝ) + 1) * a) := by
    funext m
    rw [autoCorr_geoTrain_eq_trainLagCharge hF hFc]
  rw [geoLagCharge, hterm, autoCorr_geoTrain_eq_trainLagCharge hF hFc,
    autoCorr_geoTrain_eq_trainLagCharge hF hFc] at key
  exact key

end GaloisForLFunctions.ArithmeticIncidencePositivity
