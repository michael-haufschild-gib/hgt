import GaloisForLFunctions.CompletedArithmeticForms.FinitePackets

/-!
# Exact Green inverse on irregular arithmetic nodes

Restricting the completed conductor form to increasing integer nodes replaces ordinary
second differences by differences of adjacent slopes. The exact Schur cost weights each
squared coupling difference by the reciprocal arithmetic gap, including both boundary gaps.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Adjacent slope in arithmetic position, rather than in the enumeration index. -/
def meshSlope (k : ℕ → ℕ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  (b (i + 1) - b i) / ((k (i + 1) : ℝ) - k i)

/-- The positive second difference on irregular arithmetic nodes. -/
def meshDifference (k : ℕ → ℕ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  meshSlope k b (i - 1) - meshSlope k b i

/-- Local variation divided by the actual arithmetic gaps. -/
def meshDirichletEnergy (N : ℕ) (k : ℕ → ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range N, (b (i + 1) - b i) ^ 2 / ((k (i + 1) : ℝ) - k i)

/-- Normalized completed conductor kernel at the selected nodes. -/
def meshKernel (N : ℕ) (k : ℕ → ℕ) (i j : ℕ) : ℝ :=
  min (k i : ℝ) (k j) - (k i : ℝ) * k j / k N

def meshPotential (N : ℕ) (k : ℕ → ℕ) (a : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Ico 1 N, meshKernel N k i j * a j

def meshGram (N : ℕ) (k : ℕ → ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Ico 1 N, ∑ j ∈ Ico 1 N, a i * a j * meshKernel N k i j

private theorem mesh_gap_pos {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) {i : ℕ} (hi : i < N) :
    (0 : ℝ) < (k (i + 1) : ℝ) - k i := by
  apply sub_pos.mpr
  exact_mod_cast hk (show i ≤ N by omega) (show i + 1 ≤ N by omega) (by omega)

private theorem mesh_period_pos {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) : 0 < k N := by
  have h := hk (Nat.zero_le N) le_rfl hN
  simpa only [h0] using h

private theorem mesh_nodes_interior {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) :
    ∀ i ∈ Ico 1 N, k i ∈ Ico 1 (k N) := by
  intro i hi
  rcases mem_Ico.mp hi with ⟨hi0, hiN⟩
  have hleft := hk (Nat.zero_le N) hiN.le hi0
  rw [h0] at hleft
  exact mem_Ico.mpr ⟨hleft, hk hiN.le le_rfl hiN⟩

theorem meshKernel_symm (N : ℕ) (k : ℕ → ℕ) (i j : ℕ) :
    meshKernel N k i j = meshKernel N k j i := by
  simp only [meshKernel, min_comm, mul_comm]

theorem meshKernel_zero (N : ℕ) (k : ℕ → ℕ) (h0 : k 0 = 0) (j : ℕ) :
    meshKernel N k 0 j = 0 := by
  simp [meshKernel, h0, min_eq_left (Nat.cast_nonneg (k j) : (0 : ℝ) ≤ k j)]

theorem meshKernel_endpoint {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    {j : ℕ} (hj : j ≤ N) : meshKernel N k N j = 0 := by
  have hle : (k j : ℝ) ≤ k N := by exact_mod_cast hk.monotoneOn hj le_rfl hj
  have hQ : (k N : ℝ) ≠ 0 := by exact_mod_cast (mesh_period_pos hN hk h0).ne'
  rw [meshKernel, min_eq_right hle]
  field_simp

/-- A kernel column has a unit source under the arithmetic slope difference. -/
theorem meshKernel_difference {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    {i j : ℕ} (hi : i ∈ Ico 1 N) (hj : j ∈ Ico 1 N) :
    meshDifference k (fun r => meshKernel N k r j) i = if i = j then 1 else 0 := by
  rcases mem_Ico.mp hi with ⟨hi0, hiN⟩
  rcases mem_Ico.mp hj with ⟨hj0, hjN⟩
  have hpred : i - 1 + 1 = i := Nat.sub_add_cancel hi0
  have hl : (k i : ℝ) - k (i - 1) ≠ 0 := by
    have h := mesh_gap_pos hk (show i - 1 < N by omega)
    rw [hpred] at h
    exact h.ne'
  have hr := (mesh_gap_pos hk hiN).ne'
  have hQ : (k N : ℝ) ≠ 0 := by
    exact_mod_cast (mesh_period_pos (by omega) hk h0).ne'
  have hm {r s : ℕ} (hrN : r ≤ N) (hsN : s ≤ N) (hrs : r ≤ s) :
      (k r : ℝ) ≤ k s := by exact_mod_cast hk.monotoneOn hrN hsN hrs
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [meshDifference, meshSlope, hpred, meshKernel, if_neg (ne_of_lt hij),
      min_eq_left (hm hiN.le hjN.le hij.le),
      min_eq_left (hm (r := i - 1) (s := j) (by omega) hjN.le (by omega)),
      min_eq_left (hm (r := i + 1) (s := j) (by omega) hjN.le (by omega))]
    field_simp
    <;> ring
  · simp only [meshDifference, meshSlope, hpred, meshKernel, ite_true, min_self,
      min_eq_left (hm (r := i - 1) (s := i) (by omega) hiN.le (by omega)),
      min_eq_right (hm (r := i) (s := i + 1) hiN.le (by omega) (by omega))]
    field_simp
    <;> ring
  · simp only [meshDifference, meshSlope, hpred, meshKernel, if_neg (ne_of_gt hji),
      min_eq_right (hm hjN.le hiN.le hji.le),
      min_eq_right (hm (r := j) (s := i - 1) hjN.le (by omega) (by omega)),
      min_eq_right (hm (r := j) (s := i + 1) hjN.le (by omega) (by omega))]
    field_simp
    <;> ring

private theorem meshSlope_sum {ι : Type*} (s : Finset ι) (k : ℕ → ℕ)
    (f : ι → ℕ → ℝ) (a : ι → ℝ) (i : ℕ) :
    meshSlope k (fun r => ∑ j ∈ s, f j r * a j) i =
      ∑ j ∈ s, meshSlope k (f j) i * a j := by
  unfold meshSlope
  rw [← sum_sub_distrib, sum_div]
  exact sum_congr rfl fun j _ => by ring

theorem meshPotential_difference {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) (a : ℕ → ℝ)
    {i : ℕ} (hi : i ∈ Ico 1 N) :
    meshDifference k (meshPotential N k a) i = a i := by
  have hlin : meshDifference k (meshPotential N k a) i =
      ∑ j ∈ Ico 1 N, meshDifference k (fun r => meshKernel N k r j) i * a j := by
    simp only [meshDifference, meshPotential, meshSlope_sum, sub_mul, sum_sub_distrib]
  rw [hlin]
  have he : (∑ j ∈ Ico 1 N, meshDifference k (fun r => meshKernel N k r j) i * a j) =
      ∑ j ∈ Ico 1 N, (if i = j then (1 : ℝ) else 0) * a j :=
    sum_congr rfl fun j hj => by rw [meshKernel_difference hk h0 hi hj]
  rw [he]
  simp [hi]

private theorem mesh_harmonic_affine {N : ℕ} {k : ℕ → ℕ}
    (hk : StrictMonoOn k (Set.Iic N)) (b : ℕ → ℝ)
    (hb : ∀ i ∈ Ico 1 N, meshDifference k b i = 0) :
    ∀ i, i ≤ N → b i = b 0 + meshSlope k b 0 * ((k i : ℝ) - k 0) := by
  have hs : ∀ i, i < N → meshSlope k b i = meshSlope k b 0 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have h := hb (i + 1) (mem_Ico.mpr ⟨by omega, hi⟩)
      simp only [meshDifference, Nat.add_sub_cancel] at h
      exact (sub_eq_zero.mp h).symm.trans (ih (by omega))
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hiN : i < N := by omega
    have he := div_mul_cancel₀ (b (i + 1) - b i) (mesh_gap_pos hk hiN).ne'
    change meshSlope k b i * ((k (i + 1) : ℝ) - k i) = b (i + 1) - b i at he
    rw [hs i hiN, ih (by omega)] at he
    linarith only [he]

/-- Zero-boundary arithmetic harmonic functions vanish on the entire finite mesh. -/
theorem mesh_unique {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (b c : ℕ → ℝ)
    (h0 : b 0 = c 0) (hNend : b N = c N)
    (hL : ∀ i ∈ Ico 1 N, meshDifference k b i = meshDifference k c i) :
    ∀ i, i ≤ N → b i = c i := by
  let u : ℕ → ℝ := fun i => b i - c i
  have hu0 : u 0 = 0 := sub_eq_zero.mpr h0
  have huN : u N = 0 := sub_eq_zero.mpr hNend
  have huL : ∀ i ∈ Ico 1 N, meshDifference k u i = 0 := by
    intro i hi
    have h := hL i hi
    dsimp [meshDifference, meshSlope, u] at h ⊢
    linear_combination h
  have ha := mesh_harmonic_affine hk u huL
  have hend := ha N le_rfl
  rw [hu0, huN, zero_add] at hend
  have hspan : (k N : ℝ) - k 0 ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    exact_mod_cast hk (Nat.zero_le N) le_rfl hN
  have hs : meshSlope k u 0 = 0 := (mul_eq_zero.mp hend.symm).resolve_right hspan
  intro i hi
  have h := ha i hi
  rw [hu0, hs, zero_mul, add_zero] at h
  exact sub_eq_zero.mp h

theorem meshPotential_zero (N : ℕ) (k : ℕ → ℕ) (h0 : k 0 = 0) (a : ℕ → ℝ) :
    meshPotential N k a 0 = 0 := by
  simp only [meshPotential, meshKernel_zero N k h0, zero_mul, sum_const_zero]

theorem meshPotential_endpoint {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) (a : ℕ → ℝ) :
    meshPotential N k a N = 0 := by
  apply sum_eq_zero
  intro j hj
  rw [meshKernel_endpoint hN hk h0 (mem_Ico.mp hj).2.le, zero_mul]

/-- The arithmetic slope difference is the inverse on the zero-boundary mesh domain. -/
theorem meshPotential_inverse {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    ∀ i, i ≤ N → meshPotential N k (meshDifference k b) i = b i := by
  apply mesh_unique hN hk
  · rw [meshPotential_zero N k h0, hb0]
  · rw [meshPotential_endpoint hN hk h0, hbN]
  · intro i hi
    rw [meshPotential_difference hk h0 _ hi]

private theorem mesh_green_identity (N : ℕ) (k : ℕ → ℕ) (b : ℕ → ℝ) :
    meshDirichletEnergy (N + 1) k b =
      (∑ i ∈ Icc 1 N, b i * meshDifference k b i) +
        b (N + 1) * meshSlope k b N - b 0 * meshSlope k b 0 := by
  induction N with
  | zero => simp [meshDirichletEnergy, meshSlope] <;> ring
  | succ N ih =>
    rw [meshDirichletEnergy, Finset.sum_range_succ]
    change meshDirichletEnergy (N + 1) k b +
      (b (N + 1 + 1) - b (N + 1)) ^ 2 / ((k (N + 1 + 1) : ℝ) - k (N + 1)) = _
    rw [ih, sum_Icc_succ_top (by omega)]
    simp only [meshDifference, Nat.add_sub_cancel, meshSlope]
    ring

/-- Green's identity retains both boundary slopes before imposing zero endpoint values. -/
theorem sum_mul_meshDifference {N : ℕ} (hN : 0 < N) (k : ℕ → ℕ)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    (∑ i ∈ Ico 1 N, b i * meshDifference k b i) = meshDirichletEnergy N k b := by
  rcases N with _ | N
  · omega
  have hset : Ico 1 (N + 1) = Icc 1 N := by ext i; simp
  rw [hset, mesh_green_identity, hb0, hbN, zero_mul, zero_mul, add_zero, sub_zero]

/-- The irregular mesh form is literally a completed arithmetic Gram on its selected nodes. -/
theorem meshGram_eq_completed {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) (a : ℕ → ℝ) :
    meshGram N k a =
      divisorGramEnergy (k N) (packetCoefficient (Ico 1 N) k a) / k N := by
  have hQ := mesh_period_pos hN hk h0
  have hQr : (k N : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [divisorGramEnergy_packetCoefficient (Ico 1 N) k a hQ (mesh_nodes_interior hk h0)]
  simp only [meshGram, sum_div]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [meshKernel, bridgeKernel, Nat.cast_min]
  field_simp

theorem meshGram_nonneg {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) (a : ℕ → ℝ) :
    0 ≤ meshGram N k a := by
  rw [meshGram_eq_completed hN hk h0]
  exact div_nonneg (divisorGramEnergy_nonneg _ _) (Nat.cast_nonneg _)

theorem meshGram_eq_zero_iff {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0) (a : ℕ → ℝ) :
    meshGram N k a = 0 ↔ ∀ i ∈ Ico 1 N, a i = 0 := by
  constructor
  · intro hz
    rw [meshGram_eq_completed hN hk h0] at hz
    have hQ := mesh_period_pos hN hk h0
    have hQr : (k N : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    have he := congrArg (fun r : ℝ => r * k N) hz
    rw [div_mul_cancel₀ _ hQr, zero_mul] at he
    have hc := (divisorGramEnergy_eq_zero_iff hQ _).mp he
    have hinj : Set.InjOn k (Ico 1 N : Finset ℕ) := by
      intro i hi j hj heq
      exact hk.injOn (mem_Ico.mp hi).2.le (mem_Ico.mp hj).2.le heq
    intro i hi
    have hv := hc (k i) (mesh_nodes_interior hk h0 i hi)
    rwa [packetCoefficient_at (Ico 1 N) k a hinj hi] at hv
  · intro ha
    unfold meshGram
    apply sum_eq_zero
    intro i hi
    simp only [ha i hi, zero_mul, sum_const_zero]

theorem meshGram_eq_sum_potential (N : ℕ) (k : ℕ → ℕ) (a : ℕ → ℝ) :
    meshGram N k a = ∑ i ∈ Ico 1 N, a i * meshPotential N k a i := by
  simp only [meshGram, meshPotential, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem meshPotential_sub (N : ℕ) (k : ℕ → ℕ) (a b : ℕ → ℝ) (i : ℕ) :
    meshPotential N k (fun j => a j - b j) i =
      meshPotential N k a i - meshPotential N k b i := by
  simp only [meshPotential, mul_sub, sum_sub_distrib]

theorem sum_mul_meshPotential_comm (N : ℕ) (k : ℕ → ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ Ico 1 N, a i * meshPotential N k b i) =
      ∑ i ∈ Ico 1 N, b i * meshPotential N k a i := by
  simp only [meshPotential, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [meshKernel_symm N k j i]
  ring

theorem meshGram_sub (N : ℕ) (k : ℕ → ℕ) (a b : ℕ → ℝ) :
    meshGram N k (fun i => a i - b i) = meshGram N k a -
      2 * (∑ i ∈ Ico 1 N, a i * meshPotential N k b i) + meshGram N k b := by
  simp only [meshGram_eq_sum_potential, meshPotential_sub]
  have hpoint (i : ℕ) : (a i - b i) * (meshPotential N k a i - meshPotential N k b i) =
      a i * meshPotential N k a i - a i * meshPotential N k b i -
        b i * meshPotential N k a i + b i * meshPotential N k b i := by ring
  simp_rw [hpoint]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, sum_mul_meshPotential_comm N k b a]
  ring

theorem meshGram_difference {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    meshGram N k (meshDifference k b) = meshDirichletEnergy N k b := by
  rw [meshGram_eq_sum_potential]
  calc
    _ = ∑ i ∈ Ico 1 N, b i * meshDifference k b i := by
      refine sum_congr rfl fun i hi => ?_
      rw [meshPotential_inverse hN hk h0 b hb0 hbN i (mem_Ico.mp hi).2.le]
      ring
    _ = _ := sum_mul_meshDifference hN k b hb0 hbN

/-- Exact completion at irregular arithmetic nodes, with reciprocal-gap variation cost. -/
theorem meshSchur_completion {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (a b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    meshGram N k a - 2 * (∑ i ∈ Ico 1 N, a i * b i) + meshDirichletEnergy N k b =
      meshGram N k (fun i => a i - meshDifference k b i) := by
  rw [meshGram_sub, meshGram_difference hN hk h0 b hb0 hbN]
  have hp : (∑ i ∈ Ico 1 N, a i * meshPotential N k (meshDifference k b) i) =
      ∑ i ∈ Ico 1 N, a i * b i :=
    sum_congr rfl fun i hi => by
      rw [meshPotential_inverse hN hk h0 b hb0 hbN i (mem_Ico.mp hi).2.le]
  rw [hp]

theorem meshSchur_bound {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (a b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    2 * (∑ i ∈ Ico 1 N, a i * b i) - meshGram N k a ≤ meshDirichletEnergy N k b := by
  have h := meshGram_nonneg hN hk h0 (fun i => a i - meshDifference k b i)
  rw [← meshSchur_completion hN hk h0 a b hb0 hbN] at h
  linarith only [h]

private theorem mesh_edge_square_mass {N : ℕ} (hN : 0 < N) (b : ℕ → ℝ)
    (hb0 : b 0 = 0) (hbN : b N = 0) :
    (∑ i ∈ range N, (b (i + 1) ^ 2 + b i ^ 2)) = 2 * ∑ i ∈ Ico 1 N, b i ^ 2 := by
  have hs : (∑ i ∈ range N, b (i + 1) ^ 2) = ∑ i ∈ range N, b i ^ 2 := by
    have he : (∑ i ∈ range N, b i ^ 2) - (∑ i ∈ range N, b (i + 1) ^ 2) = 0 := by
      simpa [sum_sub_distrib, hb0, hbN] using Finset.sum_range_sub' (fun i => b i ^ 2) N
    exact (sub_eq_zero.mp he).symm
  have hi : (∑ i ∈ Ico 1 N, b i ^ 2) = ∑ i ∈ range N, b i ^ 2 := by
    rw [sum_Ico_eq_sub hN]
    simp [hb0]
  rw [sum_add_distrib, hs, hi]
  ring

/-- A positive minimum arithmetic gap bounds the inverse in the coefficient norm. -/
theorem meshDirichletEnergy_le_coefficientMass {N : ℕ} (hN : 0 < N) (k : ℕ → ℕ)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i ∈ range N, δ ≤ (k (i + 1) : ℝ) - k i) :
    meshDirichletEnergy N k b ≤ (4 / δ) * ∑ i ∈ Ico 1 N, b i ^ 2 := by
  calc
    _ ≤ ∑ i ∈ range N, (2 / δ) * (b (i + 1) ^ 2 + b i ^ 2) := by
      apply sum_le_sum
      intro i hi
      have hsq : (b (i + 1) - b i) ^ 2 ≤ 2 * (b (i + 1) ^ 2 + b i ^ 2) := by
        nlinarith only [sq_nonneg (b (i + 1) + b i)]
      calc
        _ ≤ (b (i + 1) - b i) ^ 2 / δ :=
          div_le_div_of_nonneg_left (sq_nonneg _) hδ (hgap i hi)
        _ ≤ (2 * (b (i + 1) ^ 2 + b i ^ 2)) / δ :=
          div_le_div_of_nonneg_right hsq hδ.le
        _ = _ := by ring
    _ = _ := by rw [← mul_sum, mesh_edge_square_mass hN b hb0 hbN]; ring

/-- Arithmetic spacing strengthens the coefficient reserve by its minimum gap. -/
theorem meshGram_gap_coercive {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (a : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i ∈ range N, δ ≤ (k (i + 1) : ℝ) - k i) :
    (δ / 4) * (∑ i ∈ Ico 1 N, a i ^ 2) ≤ meshGram N k a := by
  let b : ℕ → ℝ := fun i => (δ / 4) * interiorExtension N a i
  have hb0 : b 0 = 0 := by simp [b, interiorExtension]
  have hbN : b N = 0 := by simp [b, interiorExtension]
  have hp : (∑ i ∈ Ico 1 N, a i * b i) = (δ / 4) * ∑ i ∈ Ico 1 N, a i ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    simp only [b, interiorExtension, if_pos hi]
    ring
  have hs : (∑ i ∈ Ico 1 N, b i ^ 2) = (δ / 4) ^ 2 * ∑ i ∈ Ico 1 N, a i ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun i hi => by simp only [b, interiorExtension, if_pos hi, mul_pow]
  have hS := meshSchur_bound hN hk h0 a b hb0 hbN
  rw [hp] at hS
  have hD := meshDirichletEnergy_le_coefficientMass hN k b hb0 hbN hδ hgap
  rw [hs] at hD
  have he (A : ℝ) : (4 / δ) * ((δ / 4) ^ 2 * A) = (δ / 4) * A := by
    field_simp
    <;> ring
  rw [he] at hD
  linarith only [hS, hD]

/-- The reciprocal-gap payment is attained and cannot be reduced uniformly. -/
theorem meshSchurCost_isGreatest {N : ℕ} {k : ℕ → ℕ}
    (hN : 0 < N) (hk : StrictMonoOn k (Set.Iic N)) (h0 : k 0 = 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hbN : b N = 0) :
    IsGreatest {r : ℝ | ∃ a : ℕ → ℝ,
      r = 2 * (∑ i ∈ Ico 1 N, a i * b i) - meshGram N k a} (meshDirichletEnergy N k b) := by
  constructor
  · refine ⟨meshDifference k b, ?_⟩
    rw [meshGram_difference hN hk h0 b hb0 hbN]
    have hp : (∑ i ∈ Ico 1 N, meshDifference k b i * b i) = meshDirichletEnergy N k b := by
      simpa only [mul_comm] using sum_mul_meshDifference hN k b hb0 hbN
    rw [hp]
    ring
  · rintro r ⟨a, rfl⟩
    exact meshSchur_bound hN hk h0 a b hb0 hbN

#print axioms meshPotential_inverse
#print axioms meshGram_eq_completed
#print axioms meshSchur_completion
#print axioms meshSchurCost_isGreatest
#print axioms meshGram_gap_coercive

end GaloisForLFunctions.CompletedArithmeticForms
