import GaloisForLFunctions.SquareRootThreshold.ReflectedClusterProducts

/-!
# A complete Weil detector with a product floor

The two reflected root products give a lower bound for the deep profile value.
The phase and tail estimates then produce a negative complete Weil form.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate BigOperators
noncomputable section
namespace SquareRootThreshold
open RHTower Zeta23

/-- Product scale retained by the halving construction. -/
def clusterProductScale (δ : ℝ) (N₀ n : ℕ) : ℝ :=
  lowHeightEps0 δ N₀ * (1 / (16 * lowHeightScale n)) ^ 2

/-- Squared profile floor including both reflected products and the phase pair. -/
def clusterProductFloor (δ : ℝ) (N₀ n : ℕ) : ℝ :=
  unitWeightFloor ^ (2 * N₀) * clusterProductScale δ N₀ n ^ (8 * n) * (δ / 2) ^ 4

theorem clusterProductScale_pos {δ : ℝ} (hδ : 0 < δ) (N₀ n : ℕ) :
    0 < clusterProductScale δ N₀ n := by
  unfold clusterProductScale lowHeightScale
  have := lowHeightEps0_pos hδ N₀
  positivity

/-- The profile retains the two products, without replacing their factors by a minimum. -/
theorem norm_sq_lowHeightProfile_product_ge {γ₀ c δ B : ℝ} {Kset : Finset ℂ} {k N₀ : ℕ}
    (hδ : 0 < δ) (hγ : 1 ≤ |γ₀|) (hB : 0 ≤ B)
    (hminus : B ≤ ∏ ρ ∈ Kset, ‖(gammaOf ρ - γ₀) - -(I * δ)‖)
    (hplus : B ≤ ∏ ρ ∈ Kset, ‖(gammaOf ρ - γ₀) - I * δ‖)
    (hk : k + 2 * (lowHeightRoots γ₀ c Kset).length + 1 = N₀) :
    unitWeightFloor ^ (2 * N₀) * B ^ 4 * δ ^ 4 ≤
      ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset) (-(I * δ))‖ ^ 2 := by
  classical
  have hW : unitWeightFloor ≤ ‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ))‖ := by
    rw [paperFT_unitWeight_neg_I_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (unitWeightFloor_le δ).trans (le_abs_self _)
  have hp : 1 ≤ ‖-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ)‖ := by
    refine hγ.trans ?_
    have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ))
    simpa using this
  have hp' : 1 ≤ ‖-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ)‖ := by
    refine hγ.trans ?_
    have := Complex.abs_re_le_norm (-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ))
    simpa using this
  have hc : δ ≤ ‖(c : ℂ) + I * δ‖ := by
    have := Complex.abs_im_le_norm ((c : ℂ) + I * δ)
    simpa [abs_of_pos hδ] using this
  have hnorm (f : ℂ → ℂ) : ‖(Kset.toList.map f).prod‖ = ∏ ρ ∈ Kset, ‖f ρ‖ := by
    have hlist : ∀ L : List ℂ, ‖(L.map f).prod‖ = (L.map fun ρ => ‖f ρ‖).prod := by
      intro L
      induction L with
      | nil => simp
      | cons ρ L ih => simpa only [List.map_cons, List.prod_cons, norm_mul] using congrArg (‖f ρ‖ * ·) ih
    rw [hlist, Finset.prod_map_toList]
  have hconj (z : ℂ) : ‖-(I * (δ : ℂ)) - conj z‖ = ‖z - I * δ‖ := by
    calc ‖-(I * (δ : ℂ)) - conj z‖ = ‖conj (-(I * (δ : ℂ)) - conj z)‖ :=
          (Complex.norm_conj _).symm
      _ = ‖I * δ - z‖ := by simp
      _ = ‖z - I * δ‖ := norm_sub_rev _ _
  have hK : B ^ 2 ≤ ‖((Kset.toList.map (fun ρ => gammaOf ρ - γ₀)).map
      (fun z => (-(I * δ) - z) * (-(I * δ) - conj z))).prod‖ := by
    rw [List.map_map, hnorm]
    simp only [Function.comp_apply, norm_mul, hconj, norm_sub_rev (-(I * (δ : ℂ)))]
    rw [Finset.prod_mul_distrib, sq]
    exact mul_le_mul hminus hplus hB (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hlow : unitWeightFloor ^ N₀ * B ^ 2 * δ ^ 2 ≤
      ‖lowHeightProfile (sinhTestWeight 1) k (lowHeightRoots γ₀ c Kset) (-(I * δ))‖ := by
    rw [lowHeightProfile_x₀_eq, hk, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      norm_mul, norm_pow]
    have hpolar : 1 ≤ ‖-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ)‖ *
        ‖-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ)‖ := by nlinarith
    calc unitWeightFloor ^ N₀ * B ^ 2 * δ ^ 2
        ≤ (‖paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ))‖ ^ N₀ *
            ‖((Kset.toList.map (fun ρ => gammaOf ρ - γ₀)).map
              (fun z => (-(I * δ) - z) * (-(I * δ) - conj z))).prod‖) *
          (‖-(I * (δ : ℂ)) - (⟨-γ₀, 1 / 2⟩ : ℂ)‖ *
            ‖-(I * (δ : ℂ)) - conj (⟨-γ₀, 1 / 2⟩ : ℂ)‖) * ‖(c : ℂ) + I * δ‖ ^ 2 := by
          have hwp := pow_le_pow_left₀ unitWeightFloor_pos.le hW N₀
          have hcp := pow_le_pow_left₀ hδ.le hc 2
          have hprod := mul_le_mul hwp hK (sq_nonneg B) (by positivity)
          have hprod0 : 0 ≤ unitWeightFloor ^ N₀ * B ^ 2 := by
            have := unitWeightFloor_pos; positivity
          have hwithpolar := le_trans hprod (le_mul_of_one_le_right (by positivity) hpolar)
          exact mul_le_mul hwithpolar hcp (sq_nonneg δ) (by positivity)
      _ = _ := by ring
  calc unitWeightFloor ^ (2 * N₀) * B ^ 4 * δ ^ 4
      = (unitWeightFloor ^ N₀ * B ^ 2 * δ ^ 2) ^ 2 := by ring
    _ ≤ _ := pow_le_pow_left₀ (by have := unitWeightFloor_pos; positivity) hlow 2

/-- A product floor larger than the complete tail gives a negative pole-killed test. -/
theorem exists_hodge_violation_cluster_product (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) {δ : ℝ} (hδ : 0 < δ) (hre : ρ₀.re = 1 / 2 + δ)
    (hγ : 2 ≤ |ρ₀.im|) {H a : ℝ} (hH : 1 ≤ H) {N₀ n : ℕ} (hN₀a : (N₀ : ℝ) ≤ a)
    (hn : (Z.finite_window (ρ₀.im - (H + 1)) (ρ₀.im + (H + 1))).toFinset.card ≤ n)
    (hNn : 2 * n + 7 ≤ N₀)
    (hbig : clusterTailConstant H (|ρ₀.im| + 1) N₀ n * (24 * A₀ * Real.log (|ρ₀.im| + 4)) <
      79 / 50 * (1 + H) ^ (4 * N₀ - 4 * n - 11) * clusterProductFloor δ N₀ n) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧ (Z.W f f).re < 0 := by
  classical
  obtain ⟨ρ₁, hρ₁, δ₁, hre₁, hδ₁, -, hγ₁, Kset, hKW, hKn, ε, η, hε0, hεε, -, hη1, hη0, hεη, hclu,
    hkil, hminus, hplus⟩ := cluster_selection_with_products (N₀ := N₀) Z hρ₀ hδ hre (by linarith) hn
      (lowHeightEps0_pos hδ N₀) le_rfl
  have hst := Z.strip ρ₁ hρ₁
  have hδ₁0 : 0 < δ₁ := by linarith
  have hδ₁2 : δ₁ ≤ 1 / 2 := by linarith [hst.2]
  obtain ⟨hsδ, hs1⟩ := lowHeightEps0_le hδ N₀
  have hγ₁' : 1 ≤ |ρ₁.im| := by
    have := abs_sub_abs_le_abs_sub ρ₀.im ρ₁.im
    rw [abs_sub_comm] at hγ₁
    linarith
  have hγ₁'' : |ρ₁.im| ≤ |ρ₀.im| + 1 := by
    have := abs_sub_abs_le_abs_sub ρ₁.im ρ₀.im
    linarith
  have hε1 : ε ≤ 1 := by
    obtain ⟨-, h⟩ := lowHeightEps0_le hδ₁0 N₀
    linarith
  have hWn : ∀ ρ, ρ ∈ (Z.finite_window (ρ₁.im - H) (ρ₁.im + H)).toFinset ↔
      ρ ∈ Z.carrier ∧ ρ₁.im - H < ρ.im ∧ ρ.im ≤ ρ₁.im + H := by
    intro ρ; rw [Set.Finite.mem_toFinset]; rfl
  have hS : (N₀ : ℝ) * (4 * ε) + (2 * (n : ℝ)) * (ε / η) + 2 * ε + 2 * ε / δ₁ ≤ 1 / 20 := by
    rw [hεη]; exact lowHeight_scale_bound hδ₁0 hε0.le hεε
  -- the phase
  obtain ⟨c, hc, hcre⟩ := exists_phase_rotation hδ₁0
    (paperFT (fun u => (sinhTestWeight 1 u : ℂ)) (-(I * δ₁)) ^
        (N₀ - (2 * (Kset.card + 2) + 1) + 2 * (Kset.card + 2) + 1) *
      ((Kset.toList.map (fun ρ => gammaOf ρ - ρ₁.im) ++ [(⟨-ρ₁.im, 1 / 2⟩ : ℂ)]).map
        (fun r => (-(I * δ₁) - r) * (-(I * δ₁) - conj r))).prod)
  have hLlen := lowHeightRoots_length ρ₁.im c Kset
  have hk : N₀ - (2 * (Kset.card + 2) + 1) + 2 * (lowHeightRoots ρ₁.im c Kset).length + 1 =
      N₀ := by
    rw [hLlen]; omega
  have hF0re : (lowHeightProfile (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
      (lowHeightRoots ρ₁.im c Kset) (-(I * δ₁))).re = 0 := by
    rw [lowHeightProfile_x₀_eq, hLlen, mul_comm]
    exact hcre
  -- the test
  obtain ⟨hfc, hfs, hff⟩ := lowHeightTest_props (sinhTestWeight_contDiff 1)
    (sinhTestWeight_even 1) (sinhTestWeight_supp zero_le_one) ρ₁.im
    (N₀ - (2 * (Kset.card + 2) + 1)) (lowHeightRoots ρ₁.im c Kset)
  refine ⟨lowHeightTest ρ₁.im (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
    (lowHeightRoots ρ₁.im c Kset), hfc, ?_, ?_, ?_, ?_⟩
  · refine tsupport_subset_of_support_subset_abs fun u hu => ?_
    have h := hfs u hu
    have e : (((N₀ - (2 * (Kset.card + 2) + 1) : ℕ) : ℝ) +
        2 * ((lowHeightRoots ρ₁.im c Kset).length : ℝ) + 1) * 1 = (N₀ : ℝ) := by
      rw [mul_one]; exact_mod_cast hk
    rw [e] at h
    linarith
  · rw [hff]
    have : I / 2 - (ρ₁.im : ℂ) = (⟨-ρ₁.im, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    exact lowHeightProfile_eq_zero_of_mem (by unfold lowHeightRoots; simp)
  · rw [hff]
    have : -(I / 2) - (ρ₁.im : ℂ) = conj (⟨-ρ₁.im, 1 / 2⟩ : ℂ) := by apply Complex.ext <;> simp
    rw [this]
    exact lowHeightProfile_eq_zero_of_conj_mem (by unfold lowHeightRoots; simp)
  · have hKH : ∀ σ ∈ Kset, σ ∈ Z.carrier ∧ |σ.im - ρ₁.im| ≤ H := by
      intro σ hσ
      obtain ⟨hσZ, h1, h2⟩ := (hWn σ).mp (hKW hσ)
      exact ⟨hσZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    have hW := re_W_lowHeightTest_le Z hA₀ hloc hρ₁ hδ₁0 hδ₁2 hre₁ hγ₁' hH hWn hKn hε0 hε1 hη0
      hclu hkil hS hk hF0re (E := 4 * N₀ - 4 * n - 11)
      (lowHeight_tail_bound_split Z (by linarith) hc hδ₁2 hKH hk hKn (by omega))
    have hscale0 := (clusterProductScale_pos hδ N₀ n).le
    have hfloor := norm_sq_lowHeightProfile_product_ge hδ₁0 hγ₁'
      (pow_nonneg hscale0 (2 * n)) hminus hplus hk
    set F2 := ‖lowHeightProfile (sinhTestWeight 1) (N₀ - (2 * (Kset.card + 2) + 1))
      (lowHeightRoots ρ₁.im c Kset) (-(I * δ₁))‖ ^ 2 with hF2
    have hcf : clusterProductFloor δ N₀ n ≤ F2 := by
      refine le_trans ?_ hfloor
      unfold clusterProductFloor
      change unitWeightFloor ^ (2 * N₀) * clusterProductScale δ N₀ n ^ (8 * n) * (δ / 2) ^ 4 ≤
        unitWeightFloor ^ (2 * N₀) * (clusterProductScale δ N₀ n ^ (2 * n)) ^ 4 * δ₁ ^ 4
      rw [← pow_mul, show 2 * n * 4 = 8 * n by omega]
      have := unitWeightFloor_pos
      gcongr
    have hHE : 0 < (1 + H) ^ (4 * N₀ - 4 * n - 11) := by positivity
    have hA0 : 0 < A₀ := by linarith
    have hlog : Real.log (|ρ₁.im| + 3) ≤ Real.log (|ρ₀.im| + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 ≤ Real.log (|ρ₁.im| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg ρ₁.im])
    have hT : clusterTailConstant H |ρ₁.im| N₀ n ≤ clusterTailConstant H (|ρ₀.im| + 1) N₀ n := by
      unfold clusterTailConstant
      gcongr
    have hT0 : 0 ≤ clusterTailConstant H |ρ₁.im| N₀ n := by
      unfold clusterTailConstant; positivity
    have hprod : clusterTailConstant H |ρ₁.im| N₀ n * (24 * A₀ * Real.log (|ρ₁.im| + 3)) ≤
        clusterTailConstant H (|ρ₀.im| + 1) N₀ n * (24 * A₀ * Real.log (|ρ₀.im| + 4)) := by
      have : 0 ≤ clusterTailConstant H (|ρ₀.im| + 1) N₀ n := hT0.trans hT
      gcongr
    have hkey : clusterTailConstant H |ρ₁.im| N₀ n / (1 + H) ^ (4 * N₀ - 4 * n - 11) *
        (24 * A₀ * Real.log (|ρ₁.im| + 3)) < 79 / 50 * F2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hHE]
      nlinarith
    linarith

end SquareRootThreshold
