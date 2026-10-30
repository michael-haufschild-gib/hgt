import GaloisForLFunctions.CompletedArithmeticForms.OptimalInterpolation

/-!
# Exact arithmetic dual costs after neutral constraints

The arithmetic Green pairing projects a coupling away from the constraint profiles.
One and two neutral constraints have attained dual costs, including dependent profiles.
The actual mass- and logarithm-neutral prime source pays the resulting projected cost.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Mixed reciprocal-gap variation on the arithmetic mesh. -/
def meshDirichletPair (N : ℕ) (k : ℕ → ℕ) (b c : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, (b (i + 1) - b i) * (c (i + 1) - c i) /
    ((k (i + 1) : ℝ) - k i)

theorem meshDirichletPair_comm (N : ℕ) (k : ℕ → ℕ) (b c : ℕ → ℝ) :
    meshDirichletPair N k b c = meshDirichletPair N k c b := by
  unfold meshDirichletPair
  exact sum_congr rfl fun i _ => by ring

theorem meshDirichletPair_self (N : ℕ) (k : ℕ → ℕ) (b : ℕ → ℝ) :
    meshDirichletPair N k b b = meshDirichletEnergy N k b := by
  unfold meshDirichletPair meshDirichletEnergy
  exact sum_congr rfl fun i _ => by ring

theorem meshDirichletEnergy_nonneg {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (b : ℕ → ℝ) :
    0 ≤ meshDirichletEnergy N k b := by
  apply sum_nonneg
  intro i hi
  have hiN := mem_range.mp hi
  have hgap : (0 : ℝ) ≤ (k (i + 1) : ℝ) - k i := by
    apply sub_nonneg.mpr
    exact_mod_cast (hk (show i ≤ N by omega) (show i + 1 ≤ N by omega) (by omega)).le
  exact div_nonneg (sq_nonneg _) hgap

theorem meshDirichletPair_sub_mul_left (N : ℕ) (k : ℕ → ℕ)
    (b g c : ℕ → ℝ) (α : ℝ) :
    meshDirichletPair N k (fun i => b i - α * g i) c =
      meshDirichletPair N k b c - α * meshDirichletPair N k g c := by
  unfold meshDirichletPair
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

theorem meshDirichletPair_sub_mul_right (N : ℕ) (k : ℕ → ℕ)
    (b c g : ℕ → ℝ) (α : ℝ) :
    meshDirichletPair N k b (fun i => c i - α * g i) =
      meshDirichletPair N k b c - α * meshDirichletPair N k b g := by
  rw [meshDirichletPair_comm, meshDirichletPair_sub_mul_left,
    meshDirichletPair_comm N k c b, meshDirichletPair_comm N k g b]

theorem meshDirichletEnergy_sub_mul (N : ℕ) (k : ℕ → ℕ)
    (b g : ℕ → ℝ) (α : ℝ) :
    meshDirichletEnergy N k (fun i => b i - α * g i) =
      meshDirichletEnergy N k b - 2 * α * meshDirichletPair N k b g +
        α ^ 2 * meshDirichletEnergy N k g := by
  unfold meshDirichletEnergy meshDirichletPair
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => by ring

private theorem mesh_mixed_green_identity (N : ℕ) (k : ℕ → ℕ) (b c : ℕ → ℝ) :
    meshDirichletPair (N + 1) k b c =
      (∑ i ∈ Icc 1 N, b i * meshDifference k c i) +
        b (N + 1) * meshSlope k c N - b 0 * meshSlope k c 0 := by
  induction N with
  | zero => simp [meshDirichletPair, meshSlope]; ring
  | succ N ih =>
    rw [meshDirichletPair, Finset.sum_range_succ]
    change meshDirichletPair (N + 1) k b c +
      (b (N + 1 + 1) - b (N + 1)) * (c (N + 1 + 1) - c (N + 1)) /
        ((k (N + 1 + 1) : ℝ) - k (N + 1)) = _
    rw [ih, sum_Icc_succ_top (by omega)]
    simp only [meshDifference, Nat.add_sub_cancel, meshSlope]
    ring

/-- Mixed Green summation retains the literal arithmetic gaps and both endpoint conditions. -/
theorem meshDirichletPair_eq_sum {N : ℕ} (hN : 0 < N) (k : ℕ → ℕ)
    (b c : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    meshDirichletPair N k b c = ∑ i ∈ Ico 1 N, b i * meshDifference k c i := by
  rcases N with _ | N
  · omega
  have hset : Ico 1 (N + 1) = Icc 1 N := by ext i; simp
  rw [hset, mesh_mixed_green_identity, hb0, hbN, zero_mul, zero_mul, add_zero, sub_zero]

/-- A zero-energy constraint pairs to zero with every zero-boundary coupling. -/
theorem meshDirichletPair_eq_zero_of_energy_eq_zero {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b g : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0)
    (hg0 : g 0 = 0) (hgN : g N = 0) (hg : meshDirichletEnergy N k g = 0) :
    meshDirichletPair N k b g = 0 := by
  have hG : meshGram N k (meshDifference k g) = 0 :=
    (meshGram_difference hN hk h0 g hg0 hgN).trans hg
  have hL := (meshGram_eq_zero_iff hN hk h0 _).mp hG
  rw [meshDirichletPair_eq_sum hN k b g hb0 hbN]
  exact sum_eq_zero fun i hi => by rw [hL i hi, mul_zero]

/-- The zero-boundary arithmetic variation has no radical at the selected nodes. -/
theorem meshDirichletEnergy_eq_zero_iff {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    meshDirichletEnergy N k b = 0 ↔ ∀ i, i ≤ N → b i = 0 := by
  constructor
  · intro hb i hi
    have hG : meshGram N k (meshDifference k b) = 0 :=
      (meshGram_difference hN hk h0 b hb0 hbN).trans hb
    have hL := (meshGram_eq_zero_iff hN hk h0 _).mp hG
    rw [← meshPotential_inverse hN hk h0 b hb0 hbN i hi]
    exact sum_eq_zero fun j hj => by rw [hL j hj, mul_zero]
  · intro hb
    apply sum_eq_zero
    intro i hi
    have hiN := mem_range.mp hi
    rw [hb (i + 1) (by omega), hb i hiN.le, sub_self, zero_pow (by omega : 2 ≠ 0), zero_div]

/-- Remove a constraint profile in the exact arithmetic dual norm; zero profiles cost zero. -/
def meshDualProjection (N : ℕ) (k : ℕ → ℕ) (g b : ℕ → ℝ) (i : ℕ) : ℝ :=
  b i - (meshDirichletPair N k b g / meshDirichletEnergy N k g) * g i

theorem meshDualProjection_zero {N : ℕ} {k : ℕ → ℕ} {g b : ℕ → ℝ}
    (hg0 : g 0 = 0) (hb0 : b 0 = 0) : meshDualProjection N k g b 0 = 0 := by
  simp only [meshDualProjection, hg0, hb0, mul_zero, sub_zero]

theorem meshDualProjection_endpoint {N : ℕ} {k : ℕ → ℕ} {g b : ℕ → ℝ}
    (hgN : g N = 0) (hbN : b N = 0) : meshDualProjection N k g b N = 0 := by
  simp only [meshDualProjection, hgN, hbN, mul_zero, sub_zero]

/-- Projection removes exactly one squared arithmetic correlation cost. -/
theorem meshDirichletEnergy_projection (N : ℕ) (k : ℕ → ℕ) (g b : ℕ → ℝ) :
    meshDirichletEnergy N k (meshDualProjection N k g b) =
      meshDirichletEnergy N k b -
        meshDirichletPair N k b g ^ 2 / meshDirichletEnergy N k g := by
  unfold meshDualProjection
  rw [meshDirichletEnergy_sub_mul]
  by_cases hg : meshDirichletEnergy N k g = 0
  · simp only [hg, div_zero, mul_zero, zero_mul, zero_pow (by omega : 2 ≠ 0), sub_zero, add_zero]
  · field_simp
    ring

/-- Removing an arithmetic constraint never increases the reciprocal-gap payment. -/
theorem meshDirichletEnergy_projection_le {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (g b : ℕ → ℝ) :
    meshDirichletEnergy N k (meshDualProjection N k g b) ≤ meshDirichletEnergy N k b := by
  rw [meshDirichletEnergy_projection]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (meshDirichletEnergy_nonneg hk g))

/-- The projected coupling is orthogonal even when the constraint profile is degenerate. -/
theorem meshDualProjection_orthogonal {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (g b : ℕ → ℝ) (hg0 : g 0 = 0) (hgN : g N = 0)
    (hb0 : b 0 = 0) (hbN : b N = 0) :
    meshDirichletPair N k (meshDualProjection N k g b) g = 0 := by
  unfold meshDualProjection
  rw [meshDirichletPair_sub_mul_left, meshDirichletPair_self]
  by_cases hg : meshDirichletEnergy N k g = 0
  · rw [meshDirichletPair_eq_zero_of_energy_eq_zero hN hk h0 b g hb0 hbN hg0 hgN hg]
    simp
  · field_simp
    ring

theorem sum_mul_meshDualProjection {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (j : ι → ℕ) (N : ℕ) (k : ℕ → ℕ) (g b : ℕ → ℝ) :
    (∑ p ∈ s, a p * meshDualProjection N k g b (j p)) =
      (∑ p ∈ s, a p * b (j p)) -
        (meshDirichletPair N k b g / meshDirichletEnergy N k g) *
          ∑ p ∈ s, a p * g (j p) := by
  unfold meshDualProjection
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun p _ => by ring

/-- The exact single-constraint dual cost is attained by the projected Green inverse. -/
theorem meshNeutralSchurCost_isGreatest {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (g b : ℕ → ℝ) (hg0 : g 0 = 0) (hgN : g N = 0)
    (hb0 : b 0 = 0) (hbN : b N = 0) :
    IsGreatest {r : ℝ | ∃ a : ℕ → ℝ, (∑ i ∈ Ico 1 N, a i * g i) = 0 ∧
      r = 2 * (∑ i ∈ Ico 1 N, a i * b i) - meshGram N k a}
      (meshDirichletEnergy N k (meshDualProjection N k g b)) := by
  let u := meshDualProjection N k g b
  have hu0 : u 0 = 0 := meshDualProjection_zero hg0 hb0
  have huN : u N = 0 := meshDualProjection_endpoint hgN hbN
  have hneutral : (∑ i ∈ Ico 1 N, meshDifference k u i * g i) = 0 := by
    rw [show (∑ i ∈ Ico 1 N, meshDifference k u i * g i) =
      ∑ i ∈ Ico 1 N, g i * meshDifference k u i from sum_congr rfl fun i _ => mul_comm _ _,
      ← meshDirichletPair_eq_sum hN k g u hg0 hgN, meshDirichletPair_comm]
    exact meshDualProjection_orthogonal hN hk h0 g b hg0 hgN hb0 hbN
  have hcoupling (a : ℕ → ℝ) (ha : (∑ i ∈ Ico 1 N, a i * g i) = 0) :
      (∑ i ∈ Ico 1 N, a i * u i) = ∑ i ∈ Ico 1 N, a i * b i := by
    change (∑ i ∈ Ico 1 N, a i * meshDualProjection N k g b (id i)) = _
    rw [sum_mul_meshDualProjection]
    simp only [id_eq, ha, mul_zero, sub_zero]
  constructor
  · refine ⟨meshDifference k u, hneutral, ?_⟩
    rw [← hcoupling _ hneutral, meshGram_difference hN hk h0 u hu0 huN]
    have hp : (∑ i ∈ Ico 1 N, meshDifference k u i * u i) = meshDirichletEnergy N k u := by
      simpa only [mul_comm] using sum_mul_meshDifference hN k u hu0 huN
    rw [hp]
    ring
  · rintro r ⟨a, ha, rfl⟩
    rw [← hcoupling a ha]
    exact meshSchur_bound hN hk h0 a u hu0 huN

/-- Successive orthogonal removal of two arithmetic moment constraints. -/
def meshDoubleProjection (N : ℕ) (k : ℕ → ℕ) (g h b : ℕ → ℝ) : ℕ → ℝ :=
  meshDualProjection N k (meshDualProjection N k g h) (meshDualProjection N k g b)

/-- Exact two-constraint cost, with no independence assumption on the profiles. -/
theorem meshDirichletEnergy_doubleProjection (N : ℕ) (k : ℕ → ℕ) (g h b : ℕ → ℝ) :
    meshDirichletEnergy N k (meshDoubleProjection N k g h b) =
      meshDirichletEnergy N k b -
        meshDirichletPair N k b g ^ 2 / meshDirichletEnergy N k g -
        meshDirichletPair N k (meshDualProjection N k g b) (meshDualProjection N k g h) ^ 2 /
          meshDirichletEnergy N k (meshDualProjection N k g h) := by
  rw [meshDoubleProjection, meshDirichletEnergy_projection, meshDirichletEnergy_projection]

/-- Both original arithmetic profiles are orthogonal to the twice-projected coupling. -/
theorem meshDoubleProjection_orthogonal {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (g h b : ℕ → ℝ) (hg0 : g 0 = 0) (hgN : g N = 0)
    (hh0 : h 0 = 0) (hhN : h N = 0) (hb0 : b 0 = 0) (hbN : b N = 0) :
    meshDirichletPair N k (meshDoubleProjection N k g h b) g = 0 ∧
      meshDirichletPair N k (meshDoubleProjection N k g h b) h = 0 := by
  let v := meshDualProjection N k g h
  let w := meshDualProjection N k g b
  let u := meshDualProjection N k v w
  have hvg : meshDirichletPair N k v g = 0 :=
    meshDualProjection_orthogonal hN hk h0 g h hg0 hgN hh0 hhN
  have hwg : meshDirichletPair N k w g = 0 :=
    meshDualProjection_orthogonal hN hk h0 g b hg0 hgN hb0 hbN
  have hug : meshDirichletPair N k u g = 0 := by
    change meshDirichletPair N k (fun i => w i -
      (meshDirichletPair N k w v / meshDirichletEnergy N k v) * v i) g = 0
    rw [meshDirichletPair_sub_mul_left, hwg, hvg, mul_zero, sub_zero]
  have huv : meshDirichletPair N k u v = 0 :=
    meshDualProjection_orthogonal hN hk h0 v w
      (meshDualProjection_zero hg0 hh0) (meshDualProjection_endpoint hgN hhN)
      (meshDualProjection_zero hg0 hb0) (meshDualProjection_endpoint hgN hbN)
  have huh : meshDirichletPair N k u h = 0 := by
    change meshDirichletPair N k u (fun i => h i -
      (meshDirichletPair N k h g / meshDirichletEnergy N k g) * g i) = 0 at huv
    rw [meshDirichletPair_sub_mul_right, hug, mul_zero, sub_zero] at huv
    exact huv
  exact ⟨hug, huh⟩

/-- Neutral couplings are unchanged by the two exact Green projections. -/
theorem sum_mul_meshDoubleProjection {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (j : ι → ℕ) (N : ℕ) (k : ℕ → ℕ) (g h b : ℕ → ℝ)
    (hg : (∑ p ∈ s, a p * g (j p)) = 0) (hh : (∑ p ∈ s, a p * h (j p)) = 0) :
    (∑ p ∈ s, a p * meshDoubleProjection N k g h b (j p)) =
      ∑ p ∈ s, a p * b (j p) := by
  rw [meshDoubleProjection, sum_mul_meshDualProjection,
    sum_mul_meshDualProjection, sum_mul_meshDualProjection, hg, hh]
  ring

/-- Both neutral constraints have an attained joint dual cost. -/
theorem meshDoubleNeutralSchurCost_isGreatest {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (g h b : ℕ → ℝ) (hg0 : g 0 = 0) (hgN : g N = 0)
    (hh0 : h 0 = 0) (hhN : h N = 0) (hb0 : b 0 = 0) (hbN : b N = 0) :
    IsGreatest {r : ℝ | ∃ a : ℕ → ℝ, (∑ i ∈ Ico 1 N, a i * g i) = 0 ∧
      (∑ i ∈ Ico 1 N, a i * h i) = 0 ∧
      r = 2 * (∑ i ∈ Ico 1 N, a i * b i) - meshGram N k a}
      (meshDirichletEnergy N k (meshDoubleProjection N k g h b)) := by
  let u := meshDoubleProjection N k g h b
  have hu0 : u 0 = 0 := meshDualProjection_zero
    (meshDualProjection_zero hg0 hh0) (meshDualProjection_zero hg0 hb0)
  have huN : u N = 0 := meshDualProjection_endpoint
    (meshDualProjection_endpoint hgN hhN) (meshDualProjection_endpoint hgN hbN)
  have horth := meshDoubleProjection_orthogonal hN hk h0 g h b hg0 hgN hh0 hhN hb0 hbN
  have hng : (∑ i ∈ Ico 1 N, meshDifference k u i * g i) = 0 := by
    simpa only [meshDirichletPair_eq_sum hN k g u hg0 hgN, mul_comm] using
      (meshDirichletPair_comm N k u g).symm.trans horth.1
  have hnh : (∑ i ∈ Ico 1 N, meshDifference k u i * h i) = 0 := by
    simpa only [meshDirichletPair_eq_sum hN k h u hh0 hhN, mul_comm] using
      (meshDirichletPair_comm N k u h).symm.trans horth.2
  have hc (a : ℕ → ℝ) (ha : (∑ i ∈ Ico 1 N, a i * g i) = 0)
      (ha' : (∑ i ∈ Ico 1 N, a i * h i) = 0) :
      (∑ i ∈ Ico 1 N, a i * u i) = ∑ i ∈ Ico 1 N, a i * b i :=
    sum_mul_meshDoubleProjection (Ico 1 N) a id N k g h b ha ha'
  constructor
  · refine ⟨meshDifference k u, hng, hnh, ?_⟩
    rw [← hc _ hng hnh, meshGram_difference hN hk h0 u hu0 huN]
    have hp : (∑ i ∈ Ico 1 N, meshDifference k u i * u i) = meshDirichletEnergy N k u := by
      simpa only [mul_comm] using sum_mul_meshDifference hN k u hu0 huN
    rw [hp]
    ring
  · rintro r ⟨a, ha, ha', rfl⟩
    rw [← hc a ha ha']
    exact meshSchur_bound hN hk h0 a u hu0 huN

/-- The joint dual radical is exactly the span of the two constraint profiles. -/
theorem meshDoubleProjection_energy_eq_zero_iff {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (g h b : ℕ → ℝ) (hg0 : g 0 = 0) (hgN : g N = 0)
    (hh0 : h 0 = 0) (hhN : h N = 0) (hb0 : b 0 = 0) (hbN : b N = 0) :
    meshDirichletEnergy N k (meshDoubleProjection N k g h b) = 0 ↔
      ∃ α β : ℝ, ∀ i ∈ Ico 1 N, b i = α * g i + β * h i := by
  let u := meshDoubleProjection N k g h b
  have hu0 : u 0 = 0 := meshDualProjection_zero
    (meshDualProjection_zero hg0 hh0) (meshDualProjection_zero hg0 hb0)
  have huN : u N = 0 := meshDualProjection_endpoint
    (meshDualProjection_endpoint hgN hhN) (meshDualProjection_endpoint hgN hbN)
  constructor
  · intro hz
    have hu := (meshDirichletEnergy_eq_zero_iff hN hk h0 u hu0 huN).mp hz
    let A := meshDirichletPair N k b g / meshDirichletEnergy N k g
    let B := meshDirichletPair N k (meshDualProjection N k g b) (meshDualProjection N k g h) /
      meshDirichletEnergy N k (meshDualProjection N k g h)
    let C := meshDirichletPair N k h g / meshDirichletEnergy N k g
    refine ⟨A - B * C, B, ?_⟩
    intro i hi
    have he := hu i (mem_Ico.mp hi).2.le
    change b i - A * g i - B * (h i - C * g i) = 0 at he
    linear_combination he
  · rintro ⟨α, β, hb⟩
    obtain ⟨a, hag, hah, he⟩ :=
      (meshDoubleNeutralSchurCost_isGreatest hN hk h0 g h b hg0 hgN hh0 hhN hb0 hbN).1
    have hc : (∑ i ∈ Ico 1 N, a i * b i) = 0 := by
      calc
        _ = α * (∑ i ∈ Ico 1 N, a i * g i) + β * (∑ i ∈ Ico 1 N, a i * h i) := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun i hi => by rw [hb i hi]; ring
        _ = 0 := by rw [hag, hah]; ring
    rw [hc] at he
    have hG := meshGram_nonneg hN hk h0 a
    have hD := meshDirichletEnergy_nonneg hk u
    change meshDirichletEnergy N k u = _ at he ⊢
    linarith only [he, hG, hD]

/-- Zero-endpoint mass and logarithmic profiles on an arithmetic mesh. -/
def meshPrimeNeutralProjection (N : ℕ) (k : ℕ → ℕ) (b : ℕ → ℝ) : ℕ → ℝ :=
  meshDoubleProjection N k (interiorExtension N (fun _ => 1))
    (interiorExtension N (fun i => Real.log (k i))) b

theorem meshPrimeNeutralProjection_energy_le {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (b : ℕ → ℝ) :
    meshDirichletEnergy N k (meshPrimeNeutralProjection N k b) ≤ meshDirichletEnergy N k b := by
  exact (meshDirichletEnergy_projection_le hk _ _).trans (meshDirichletEnergy_projection_le hk _ _)

/-- The actual prime source pays a coupling by its mass- and logarithm-quotient Green norm. -/
theorem primePacket_neutral_mesh_schur_bound (S : Finset Nat.Primes) (a : Nat.Primes → ℝ)
    {P N : ℕ} {k : ℕ → ℕ} (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N))
    (h0 : k 0 = 0) (hQ : k N = 2 * P + 2)
    (hS : ∀ p ∈ S, P < (p : ℕ) ∧ (p : ℕ) ≤ 2 * P)
    (hA : BezoutValuationIncidence.primePacketMass S a = 0)
    (hL : BezoutValuationIncidence.primePacketLogMoment S a = 0)
    (j : Nat.Primes → ℕ) (hj : ∀ p ∈ S, j p ∈ Ico 1 N)
    (hnode : ∀ p ∈ S, k (j p) = (p : ℕ))
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    2 * (∑ p ∈ S, a p * b (j p)) -
      BezoutValuationIncidence.primePacketBilinear S S a a ≤
        meshDirichletEnergy N k (meshPrimeNeutralProjection N k b) := by
  let g := interiorExtension N (fun _ => (1 : ℝ))
  let h := interiorExtension N (fun i => Real.log (k i))
  have hg0 : g 0 = 0 := by simp [g, interiorExtension]
  have hgN : g N = 0 := by simp [g, interiorExtension]
  have hh0 : h 0 = 0 := by simp [h, interiorExtension]
  have hhN : h N = 0 := by simp [h, interiorExtension]
  have hag : (∑ p ∈ S, a p * g (j p)) = 0 := by
    have he : (∑ p ∈ S, a p * g (j p)) = ∑ p ∈ S, a p := by
      exact sum_congr rfl fun p hp => by simp only [g, interiorExtension, if_pos (hj p hp), mul_one]
    rw [he]
    exact hA
  have hah : (∑ p ∈ S, a p * h (j p)) = 0 := by
    have he : (∑ p ∈ S, a p * h (j p)) =
        ∑ p ∈ S, a p * Real.log (p : ℕ) := by
      exact sum_congr rfl fun p hp => by simp only [h, interiorExtension, if_pos (hj p hp), hnode p hp]
    rw [he]
    exact hL
  have hu0 : meshPrimeNeutralProjection N k b 0 = 0 := meshDualProjection_zero
    (meshDualProjection_zero hg0 hh0) (meshDualProjection_zero hg0 hb0)
  have huN : meshPrimeNeutralProjection N k b N = 0 := meshDualProjection_endpoint
    (meshDualProjection_endpoint hgN hhN) (meshDualProjection_endpoint hgN hbN)
  have hs := primePacket_mesh_schur_bound S a hN hk h0 hQ hS hA hL j hj hnode
    (meshPrimeNeutralProjection N k b) hu0 huN
  have hc := sum_mul_meshDoubleProjection S a j N k g h b hag hah
  change (∑ p ∈ S, a p * meshPrimeNeutralProjection N k b (j p)) = _ at hc
  rwa [hc] at hs

#print axioms meshDirichletPair_eq_sum
#print axioms meshNeutralSchurCost_isGreatest
#print axioms meshDoubleNeutralSchurCost_isGreatest
#print axioms meshDirichletEnergy_doubleProjection
#print axioms meshDoubleProjection_energy_eq_zero_iff
#print axioms primePacket_neutral_mesh_schur_bound

end GaloisForLFunctions.CompletedArithmeticForms
