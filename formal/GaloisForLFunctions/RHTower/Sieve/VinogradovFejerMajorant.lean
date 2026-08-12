import GaloisForLFunctions.RHTower.Sieve.PhaseGeometricBound
import GaloisForLFunctions.RHTower.Sieve.VinogradovWideDifference

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

def vinogradovFejerCoordinateBound
    (N b : ℕ) {k : ℕ} (j : Fin k) : ℕ :=
  b * N ^ (j.val + 1)

def vinogradovFejerLength
    (N b : ℕ) {k : ℕ} (j : Fin k) : ℕ :=
  2 * vinogradovFejerCoordinateBound N b j + 1

def vinogradovFejerRadius (N b k : ℕ) : ℕ :=
  2 * b * N ^ k

theorem vinogradovPowerSum_le_coordinate
    {N b k : ℕ} (u : Fin b → Fin N) (j : Fin k) :
    (∑ i : Fin b, (u i).val ^ (j.val + 1)) ≤
      vinogradovFejerCoordinateBound N b j := by
  have hterm : ∀ i : Fin b,
      (u i).val ^ (j.val + 1) ≤ N ^ (j.val + 1) := by
    intro i
    exact Nat.pow_le_pow_left (Nat.le_of_lt (u i).isLt) _
  calc
    _ ≤ ∑ _i : Fin b, N ^ (j.val + 1) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = b * N ^ (j.val + 1) := by simp
    _ = vinogradovFejerCoordinateBound N b j := rfl

theorem vinogradovFejerCoordinateBound_le_radius
    {N b k : ℕ} (hN : N ≠ 0) (j : Fin k) :
    2 * vinogradovFejerCoordinateBound N b j ≤
      vinogradovFejerRadius N b k := by
  have hexp : j.val + 1 ≤ k := j.isLt
  have hpow : N ^ (j.val + 1) ≤ N ^ k :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN) hexp
  unfold vinogradovFejerCoordinateBound vinogradovFejerRadius
  simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * b) hpow

theorem vinogradovRawDifference_le_fejerRadius (N b k : ℕ) :
    b * N ^ k ≤ vinogradovFejerRadius N b k := by
  unfold vinogradovFejerRadius
  rw [show 2 * b * N ^ k = 2 * (b * N ^ k) by ring]
  omega

theorem vinogradovFejerLength_ne_zero
    (N b : ℕ) {k : ℕ} (j : Fin k) :
    vinogradovFejerLength N b j ≠ 0 := by
  unfold vinogradovFejerLength
  omega

def vinogradovFejerCoordinateSignature
    {N b k : ℕ} (hN : N ≠ 0) (j : Fin k)
    (ab : Fin (vinogradovFejerLength N b j) ×
      Fin (vinogradovFejerLength N b j)) :
    Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius N b k)) :=
  ⟨ab.1.val + vinogradovFejerRadius N b k - ab.2.val, by
    have hcoord := vinogradovFejerCoordinateBound_le_radius (b := b) hN j
    have ha : ab.1.val ≤ 2 * vinogradovFejerCoordinateBound N b j := by
      have haLt := ab.1.isLt
      unfold vinogradovFejerLength at haLt
      omega
    have hb : ab.2.val ≤ 2 * vinogradovFejerCoordinateBound N b j := by
      have hbLt := ab.2.isLt
      unfold vinogradovFejerLength at hbLt
      omega
    have hbR : ab.2.val ≤ vinogradovFejerRadius N b k := hb.trans hcoord
    unfold vinogradovWideDifferenceBoxSize
    calc
      ab.1.val + vinogradovFejerRadius N b k - ab.2.val ≤
          ab.1.val + vinogradovFejerRadius N b k := Nat.sub_le _ _
      _ ≤ vinogradovFejerRadius N b k + vinogradovFejerRadius N b k :=
        Nat.add_le_add_right (ha.trans hcoord) _
      _ = 2 * vinogradovFejerRadius N b k := by omega
      _ < 2 * vinogradovFejerRadius N b k + 1 := Nat.lt_succ_self _⟩

def vinogradovFejerShiftEmbedding
    {N b k : ℕ} (hN : N ≠ 0)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) (j : Fin k) :
    Fin (vinogradovFejerCoordinateBound N b j + 1) ↪
      {ab : Fin (vinogradovFejerLength N b j) ×
          Fin (vinogradovFejerLength N b j) //
        vinogradovFejerCoordinateSignature hN j ab =
          vinogradovWideDifferenceSignature hN
            (vinogradovRawDifference_le_fejerRadius N b k) uv j} where
  toFun t := ⟨
    (⟨(∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + t.val, by
        have hu := vinogradovPowerSum_le_coordinate uv.1 j
        unfold vinogradovFejerLength
        omega⟩,
      ⟨(∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) + t.val, by
        have hv := vinogradovPowerSum_le_coordinate uv.2 j
        unfold vinogradovFejerLength
        omega⟩),
    by
      apply Fin.ext
      dsimp [vinogradovFejerCoordinateSignature,
        vinogradovWideDifferenceSignature]
      have hu := vinogradovPowerSum_le_coordinate uv.1 j
      have hv := vinogradovPowerSum_le_coordinate uv.2 j
      have hcoord := vinogradovFejerCoordinateBound_le_radius (b := b) hN j
      have ht : t.val ≤ vinogradovFejerCoordinateBound N b j := by omega
      have hvR :
          (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) + t.val ≤
            vinogradovFejerRadius N b k := by
        calc
          _ ≤ 2 * vinogradovFejerCoordinateBound N b j := by omega
          _ ≤ vinogradovFejerRadius N b k := hcoord
      omega⟩
  inj' := by
    intro s t h
    have hfirst := congrArg
      (fun z : {ab : Fin (vinogradovFejerLength N b j) ×
          Fin (vinogradovFejerLength N b j) //
        vinogradovFejerCoordinateSignature hN j ab =
          vinogradovWideDifferenceSignature hN
            (vinogradovRawDifference_le_fejerRadius N b k) uv j} =>
        z.1.1.val) h
    apply Fin.ext
    dsimp at hfirst
    omega

theorem card_vinogradovFejerCoordinateFiber_ge
    {N b k : ℕ} (hN : N ≠ 0)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) (j : Fin k) :
    vinogradovFejerCoordinateBound N b j + 1 ≤
      Fintype.card {ab : Fin (vinogradovFejerLength N b j) ×
          Fin (vinogradovFejerLength N b j) //
        vinogradovFejerCoordinateSignature hN j ab =
          vinogradovWideDifferenceSignature hN
            (vinogradovRawDifference_le_fejerRadius N b k) uv j} := by
  simpa using Fintype.card_le_of_embedding
    (vinogradovFejerShiftEmbedding hN uv j)

def vinogradovFejerCoordinateWeight
    {N b k : ℕ} (hN : N ≠ 0) (j : Fin k)
    (l : Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius N b k))) : ℝ :=
  (2 / (vinogradovFejerLength N b j : ℝ)) *
    Fintype.card {ab : Fin (vinogradovFejerLength N b j) ×
        Fin (vinogradovFejerLength N b j) //
      vinogradovFejerCoordinateSignature hN j ab = l}

theorem vinogradovFejerCoordinateWeight_nonneg
    {N b k : ℕ} (hN : N ≠ 0) (j : Fin k)
    (l : Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius N b k))) :
    0 ≤ vinogradovFejerCoordinateWeight hN j l := by
  unfold vinogradovFejerCoordinateWeight
  positivity

theorem one_le_vinogradovFejerCoordinateWeight_signature
    {N b k : ℕ} (hN : N ≠ 0)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) (j : Fin k) :
    1 ≤ vinogradovFejerCoordinateWeight hN j
      (vinogradovWideDifferenceSignature hN
        (vinogradovRawDifference_le_fejerRadius N b k) uv j) := by
  let B := vinogradovFejerCoordinateBound N b j
  let H := vinogradovFejerLength N b j
  let C := Fintype.card {ab : Fin H × Fin H //
    vinogradovFejerCoordinateSignature hN j ab =
      vinogradovWideDifferenceSignature hN
        (vinogradovRawDifference_le_fejerRadius N b k) uv j}
  have hcard : B + 1 ≤ C := by
    simpa [B, H, C] using card_vinogradovFejerCoordinateFiber_ge hN uv j
  have hH : (H : ℝ) = 2 * B + 1 := by
    simp [H, B, vinogradovFejerLength]
  have hHr : (0 : ℝ) < H := by
    rw [hH]
    positivity
  unfold vinogradovFejerCoordinateWeight
  change 1 ≤ (2 / (H : ℝ)) * (C : ℝ)
  have hcardr : (B + 1 : ℝ) ≤ C := by exact_mod_cast hcard
  calc
    1 ≤ (2 / (H : ℝ)) * (B + 1 : ℝ) := by
      rw [hH]
      rw [div_mul_eq_mul_div,
        le_div_iff₀ (by positivity : (0 : ℝ) < 2 * B + 1)]
      nlinarith
    _ ≤ (2 / (H : ℝ)) * (C : ℝ) := by gcongr

def vinogradovFejerWeight
    {N b k : ℕ} (hN : N ≠ 0)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius N b k))) : ℝ :=
  ∏ j : Fin k, vinogradovFejerCoordinateWeight hN j (l j)

theorem vinogradovFejerWeight_nonneg
    {N b k : ℕ} (hN : N ≠ 0)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize
      (vinogradovFejerRadius N b k))) :
    0 ≤ vinogradovFejerWeight hN l := by
  exact Finset.prod_nonneg fun j _ => vinogradovFejerCoordinateWeight_nonneg hN j (l j)

/-- Constructive Fejér majorant on every actual Vinogradov difference vector.
No triangular-coefficient formula or absolute-value case split is needed. -/
theorem one_le_vinogradovFejerWeight_signature
    {N b k : ℕ} (hN : N ≠ 0)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) :
    1 ≤ vinogradovFejerWeight hN
      (vinogradovWideDifferenceSignature hN
        (vinogradovRawDifference_le_fejerRadius N b k) uv) := by
  unfold vinogradovFejerWeight
  simpa only [Finset.prod_const_one] using
    Finset.prod_le_prod (fun _ _ => zero_le_one)
      (fun j _ => one_le_vinogradovFejerCoordinateWeight_signature hN uv j)

end

end RHTower.Sieve
