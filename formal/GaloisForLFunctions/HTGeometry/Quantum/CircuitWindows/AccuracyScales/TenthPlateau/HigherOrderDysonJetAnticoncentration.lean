import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.MicroCollarBipolarCodimension
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.HiddenRotatedIsingTube
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.DerivChain
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.PolynomialGood
import GaloisForLFunctions.HTGeometry.PolynomialExtrapolationRemez
import Mathlib.GroupTheory.Perm.Fin

/-! # Higher-order Dyson jet anti-concentration, Pólya–Lagrange bounds, and `2`-local escape at 1/10

This module develops higher-order derivative-chain and unitary-jet anti-concentration for spectral
min-max heights around `e = 1 / 10`, replacing `2^{-O(N)}`-radius Lipschitz Kato charts by global
`1`D slice anti-concentration and resolving both what higher-order Dyson variations achieve and the
exact `U(2)^⊗N` gauge and active-budget obstructions:

1. **Upper-bound-free Pólya–Lagrange sublevel inequality and Gaussian slice anti-concentration:**
   - `polya_lagrange_derivChain_sublevel_le`: for any `k ≥ 1`, `OrdConnected` domain `I ⊆ ℝ`
     (bounded or unbounded), and `IsDerivChain k F I` with `∀ t ∈ I, c_k ≤ |F k t|` (`c_k > 0`,
     with **no** upper bound on `|F_k|`),
     `volume {t ∈ I | |F 0 t| ≤ ε} ≤ ENNReal.ofReal (4 * k * (ε / c_k) ^ (1 / k))`
     (eliminating the `k!` loss via `sum_inv_prod_erase_abs_sub_fin`).
   - `gaussian_higherDeriv_piecewise_anticoncentration`,
     `order_N_exponential_anticoncentration_at_quadraticScale`,
     `fixed_tenth_locking_of_higherDeriv_sublinearOrder`, and
     `order_N_cannot_absorb_activeBudgets_under_compilerCap`:
     `M`-piece Gaussian anti-concentration `≤ ∑ m, (4 * k_m / √(2 π)) * (δ / (2 * c)) ^ (1 / k_m)`,
     yielding `2^{-(b - γ) N}` single-budget decay at `k = N`, `δ = 2^{-b N²}`, `M ≤ 2^{γ N}`,
     and full active-budget locking `m_{1/10 + δ_quad} = m_{1/10}` across all `Q asymp 4^N` budgets
     at sublinear orders `1 ≤ k ≤ ⌊b / (3 N)⌋₊`, whereas under the quadratic compiler cap
     `b ≤ N² / 25`, `(2^{-b})^{1/N} ≥ 2^{-N / 25}` cannot absorb `Q ≥ 4^N` at `k = N`.
2. **Higher-order unitary-jet Danskin (`s = u^m`) and Hölder-Dini collar anti-concentration:**
   - `unitaryJet_isSelfAdjoint` and `liminf_torusCriticalHeight_higherOrderUnitaryJet_ge`:
     if `V : ℝ → UGroup N` satisfies `‖V(u) - (V(0) + u^m • M_m)‖ / u^m → 0` as `u → 0⁺`, then
     `K_m := i • (M_m * star V(0))` is self-adjoint and `s ↦ torusCriticalHeight e (V (s^{1/m})) j`
     obeys the exact `m`-th order Danskin lower Dini bound at `s = 0⁺` without `C_j` `ε`-nets.
   - `holder_dini_collar_diam_le` and `gaussian_holder_dini_collar_anticoncentration`:
     right Dini coercivity `≥ c_m > 0` in `s = u^m` confines `(e₀, e₀ + δ]` visits on `[0, R]` to
     diameter `≤ (δ / c_m) ^ (1 / m)`.
3. **`U(2)^⊗N` left-invariance obstruction of `1`-local spin-flip lines vs. `2`-local Dyson escape:**
   - `torusCriticalHeight_prodLocal_left_eq` and `torusCriticalHeight_const_along_localUnitary_curve`:
     left multiplication of `V : UGroup N` by any heterogeneous local unitary `prodLocalMatrix R`
     preserves `torusCriticalHeight e · j` identically, forcing every `1`-local spin-flip eigenbasis
     curve to have identically constant `torusCriticalHeight` to all orders `k ≥ 1`.
   - `euler_shuffle_reciprocal_sum` and `twoLocal_secondOrder_dyson_escapes_hammingThree_blindSpot`:
     exact `m!`-term Euler-shuffle identity `∑_{π ∈ S_m} ∏_{r=0}^{m-1} (∑_{j ≥ r} B_{π(j)})⁻¹ =
     ∏_{j=0}^{m-1} B_j⁻¹`, and explicit escape of `V_chain = X_0 X_1 + X_2 ∈ PathShell n` (`N ≥ 3`)
     from the Hamming-distance-`3` first-order Kato blind spot at second Dyson order
     (`secondOrderDysonOffDiag = 1 / 48 ≠ 0`) while generating non-product `2`-qubit entanglement. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix Polynomial
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate Nat
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev UGroup (N : ℕ) := Matrix.unitaryGroup (Config N) ℂ
private abbrev StateSpace (N : ℕ) := EuclideanSpace ℂ (Config N)
private abbrev Realizes {n : ℕ} := @DiagonalSynthesis.Realizes n

/-! ## Section 1: Pólya–Lagrange higher-derivative sublevel bound and Gaussian anti-concentration -/

private theorem coeff_lagrangeBasis_top {k : ℕ} (v : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    (Lagrange.basis Finset.univ v i).coeff k =
      ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹ := by
  classical
  let s : Finset (Fin (k + 1)) := Finset.univ.erase i
  let c : Fin (k + 1) → ℝ := fun j => (v i - v j)⁻¹
  have hcard : s.card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hbasis : Lagrange.basis Finset.univ v i =
      C (∏ j ∈ s, c j) * ∏ j ∈ s, (X - C (v j)) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, s, c]
    rw [Finset.prod_mul_distrib, map_prod]
  let W_i : ℝ[X] := ∏ j ∈ s, (X - C (v j))
  have hmon : W_i.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C (v j)
  have hdeg : W_i.natDegree = k := by
    dsimp [W_i]
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C (v j))]
    have h1 : (∑ j ∈ s, (X - C (v j)).natDegree) = ∑ _j ∈ s, 1 :=
      Finset.sum_congr rfl fun j _ => Polynomial.natDegree_X_sub_C (v j)
    rw [h1, Finset.sum_const, hcard, smul_eq_mul, mul_one]
  have hW_coeff : W_i.coeff k = 1 := by
    rw [← hdeg]; exact hmon.coeff_natDegree
  rw [hbasis]
  change (C (∏ j ∈ s, c j) * W_i).coeff k = ∏ j ∈ s, c j
  rw [Polynomial.coeff_C_mul, hW_coeff, mul_one]

private theorem polya_lagrange_bounded_sublevel_le {k : ℕ} (hk : 1 ≤ k)
    {I : Set ℝ} (hI : I.OrdConnected) {F : ℕ → ℝ → ℝ}
    (hF : KleinbockMargulis.IsDerivChain k F I)
    {c_k ε : ℝ} (hc : 0 < c_k) (hε : 0 ≤ ε)
    (hderiv : ∀ t ∈ I, c_k ≤ |F k t|)
    (hfin : volume {t ∈ I | |F 0 t| ≤ ε} ≠ ⊤) :
    (volume {t ∈ I | |F 0 t| ≤ ε}).toReal ≤
      4 * (k : ℝ) * (ε / c_k) ^ ((k : ℝ)⁻¹) := by
  classical
  let S : Set ℝ := {t ∈ I | |F 0 t| ≤ ε}
  let r₀ : ℝ := (ε / c_k) ^ ((k : ℝ)⁻¹)
  have hr₀_nn : 0 ≤ r₀ := Real.rpow_nonneg (div_nonneg hε hc.le) _
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  by_contra hgt
  push Not at hgt
  let m_vol : ℝ := (volume S).toReal
  change 4 * (k : ℝ) * r₀ < m_vol at hgt
  have hdiv_gt : 2 * r₀ < m_vol / (2 * (k : ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith only [hgt]
  let δ : ℝ := (2 * r₀ + m_vol / (2 * (k : ℝ))) / 2
  have hδ_gt : 2 * r₀ < δ := by dsimp [δ]; linarith only [hdiv_gt]
  have hδ_pos : 0 < δ := lt_of_le_of_lt (by positivity) hδ_gt
  have hsepm : 2 * (k : ℝ) * δ < (volume S).toReal := by
    have hlt : δ < m_vol / (2 * (k : ℝ)) := by dsimp [δ]; linarith only [hdiv_gt]
    have h1 := mul_lt_mul_of_pos_left hlt (by positivity : 0 < 2 * (k : ℝ))
    have h2 : 2 * (k : ℝ) * (m_vol / (2 * (k : ℝ))) = m_vol := by
      field_simp [hk_pos.ne']
    rwa [h2] at h1
  obtain ⟨T, hTS, hTcard, hTsep⟩ :=
    KleinbockMargulis.exists_finset_separated hδ_pos k hsepm
  let w := T.orderEmbOfFin hTcard
  let v : Fin (k + 1) → ℝ := fun i => w i
  have hv_mono : StrictMono v := fun i j hij => w.strictMono hij
  have hv_S : ∀ i : Fin (k + 1), v i ∈ S :=
    fun i => hTS (Finset.orderEmbOfFin_mem T hTcard i)
  have hv_I : ∀ i : Fin (k + 1), v i ∈ I := fun i => (hv_S i).1
  have hv_le : ∀ i : Fin (k + 1), |F 0 (v i)| ≤ ε := fun i => (hv_S i).2
  have hv_sep : ∀ i j : Fin (k + 1), |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| * δ ≤ |v i - v j| := by
    intro i j
    rcases le_total i j with hij | hji
    · have h1 := orderEmbOfFin_index_sep T hTcard hTsep i j hij
      have hij_r : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (show (i : ℕ) ≤ j from hij)
      have hv_ij : v i ≤ v j := hv_mono.monotone hij
      rw [abs_sub_comm ((i : ℕ) : ℝ), abs_of_nonneg (sub_nonneg.mpr hij_r),
        abs_sub_comm (v i), abs_of_nonneg (sub_nonneg.mpr hv_ij)]
      exact h1
    · have h1 := orderEmbOfFin_index_sep T hTcard hTsep j i hji
      have hji_r : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast (show (j : ℕ) ≤ i from hji)
      have hv_ji : v j ≤ v i := hv_mono.monotone hji
      rw [abs_of_nonneg (sub_nonneg.mpr hji_r), abs_of_nonneg (sub_nonneg.mpr hv_ji)]
      exact h1
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ :=
    KleinbockMargulis.exists_chain_eq_factorial_mul_coeff hI k hF v hv_mono hv_I
  have hξ_I : ξ ∈ I := hI.out (hv_I 0) (hv_I (Fin.last k)) hξ_mem
  let P : ℝ[X] := Lagrange.interpolate Finset.univ v fun i => F 0 (v i)
  have hP_coeff : P.coeff k =
      ∑ i : Fin (k + 1), F 0 (v i) * ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹ := by
    dsimp [P]
    rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.coeff_smul, smul_eq_mul, coeff_lagrangeBasis_top]
  have hterm_le (i : Fin (k + 1)) :
      |F 0 (v i) * ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹| ≤
        ε * (δ⁻¹ ^ k * (∏ j ∈ Finset.univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹) := by
    rw [abs_mul, Finset.abs_prod]
    have hcard_er : (Finset.univ.erase i).card = k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have hprod_le : (∏ j ∈ Finset.univ.erase i, |(v i - v j)⁻¹|) ≤
        δ⁻¹ ^ k * (∏ j ∈ Finset.univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
      calc (∏ j ∈ Finset.univ.erase i, |(v i - v j)⁻¹|)
          ≤ ∏ j ∈ Finset.univ.erase i, (δ⁻¹ * |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|⁻¹) := by
            refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => ?_
            have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
            have hij_pos : 0 < |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
              rw [abs_pos, sub_ne_zero]
              exact fun h => hne (Fin.ext (by exact_mod_cast h))
            rw [abs_inv, ← mul_inv, mul_comm δ⁻¹]
            exact inv_anti₀ (mul_pos hij_pos hδ_pos) (hv_sep i j)
        _ = δ⁻¹ ^ k * (∏ j ∈ Finset.univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹ := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, hcard_er, Finset.prod_inv_distrib]
    exact mul_le_mul (hv_le i) hprod_le (Finset.prod_nonneg fun _ _ => abs_nonneg _) hε
  have hcoeff_le : |P.coeff k| ≤ ε * (2 / δ) ^ k / (k ! : ℝ) := by
    rw [hP_coeff]
    calc |∑ i : Fin (k + 1), F 0 (v i) * ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹|
        ≤ ∑ i : Fin (k + 1), |F 0 (v i) * ∏ j ∈ Finset.univ.erase i, (v i - v j)⁻¹| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (k + 1),
            ε * (δ⁻¹ ^ k * (∏ j ∈ Finset.univ.erase i, |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)|)⁻¹) :=
          Finset.sum_le_sum fun i _ => hterm_le i
      _ = ε * δ⁻¹ ^ k * (2 ^ k / (k ! : ℝ)) := by
          rw [← sum_inv_prod_erase_abs_sub_fin k, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ε * (2 / δ) ^ k / (k ! : ℝ) := by
          rw [div_pow, inv_pow]; ring
  have hfac_pos : (0 : ℝ) < (k ! : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hFk_le : |F k ξ| ≤ ε * (2 / δ) ^ k := by
    change F k ξ = (k ! : ℝ) * P.coeff k at hξ_eq
    rw [hξ_eq, abs_mul, abs_of_pos hfac_pos]
    calc (k ! : ℝ) * |P.coeff k|
        ≤ (k ! : ℝ) * (ε * (2 / δ) ^ k / (k ! : ℝ)) :=
          mul_le_mul_of_nonneg_left hcoeff_le hfac_pos.le
      _ = ε * (2 / δ) ^ k := mul_div_cancel₀ _ hfac_pos.ne'
  have hc_le : c_k ≤ ε * (2 / δ) ^ k := (hderiv ξ hξ_I).trans hFk_le
  rcases eq_or_lt_of_le hε with rfl | hε_pos
  · rw [zero_mul] at hc_le; linarith only [hc, hc_le]
  · have hr₀_pow : r₀ ^ k = ε / c_k := by
      dsimp [r₀]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hε_pos.le hc.le),
        inv_mul_cancel₀ hk_pos.ne', Real.rpow_one]
    have hpow_lt : (2 * r₀) ^ k < δ ^ k :=
      pow_lt_pow_left₀ hδ_gt (by positivity) (by omega)
    rw [mul_pow, hr₀_pow] at hpow_lt
    have hlt_ck : ε * (2 / δ) ^ k < c_k := by
      rw [div_pow, mul_div_assoc, div_lt_iff₀ (pow_pos hδ_pos k)]
      have h1 : (2 : ℝ) ^ k * (ε / c_k) * c_k = ε * (2 : ℝ) ^ k := by
        field_simp [hc.ne']
      nlinarith only [hpow_lt, hc, h1]
    linarith only [hc_le, hlt_ck]

/-- Upper-bound-free Pólya–Lagrange sublevel inequality on arbitrary `OrdConnected` domains `I ⊆ ℝ`:
for any `k ≥ 1`, `IsDerivChain k F I` with `∀ t ∈ I, c_k ≤ |F k t|` (`c_k > 0`), and `ε ≥ 0`,
`volume {t ∈ I | |F 0 t| ≤ ε} ≤ ENNReal.ofReal (4 * k * (ε / c_k) ^ (1 / k))`
and `(volume {t ∈ I | |F 0 t| ≤ ε}).toReal ≤ 4 * k * (ε / c_k) ^ (1 / k)`. -/
theorem polya_lagrange_derivChain_sublevel_le {k : ℕ} (hk : 1 ≤ k)
    {I : Set ℝ} (hI : I.OrdConnected) {F : ℕ → ℝ → ℝ}
    (hF : KleinbockMargulis.IsDerivChain k F I)
    {c_k ε : ℝ} (hc : 0 < c_k) (hε : 0 ≤ ε)
    (hderiv : ∀ t ∈ I, c_k ≤ |F k t|) :
    let B := 4 * (k : ℝ) * (ε / c_k) ^ ((k : ℝ)⁻¹)
    volume {t ∈ I | |F 0 t| ≤ ε} ≤ ENNReal.ofReal B ∧
    (volume {t ∈ I | |F 0 t| ≤ ε}).toReal ≤ B := by
  intro B
  have hB_nn : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg hε hc.le) _)
  let S_trunc (R : ℕ) : Set ℝ := {t ∈ I ∩ Icc (-(R : ℝ)) (R : ℝ) | |F 0 t| ≤ ε}
  have hmono : Monotone S_trunc := by
    intro R₁ R₂ hR t ht
    have hR_real : (R₁ : ℝ) ≤ (R₂ : ℝ) := Nat.cast_le.mpr hR
    exact ⟨⟨ht.1.1, by linarith only [ht.1.2.1, hR_real], by linarith only [ht.1.2.2, hR_real]⟩, ht.2⟩
  have hunion : (⋃ R : ℕ, S_trunc R) = {t ∈ I | |F 0 t| ≤ ε} := by
    ext t
    simp only [mem_iUnion, S_trunc, mem_setOf_eq, mem_inter_iff, mem_Icc]
    refine ⟨fun ⟨_, ⟨htI, _⟩, htF⟩ => ⟨htI, htF⟩, fun ⟨htI, htF⟩ => ?_⟩
    obtain ⟨R, hR⟩ := exists_nat_ge |t|
    have habs := abs_le.mp hR
    exact ⟨R, ⟨htI, habs.1, habs.2⟩, htF⟩
  have htrunc_le (R : ℕ) : volume (S_trunc R) ≤ ENNReal.ofReal B := by
    have hsub_box : S_trunc R ⊆ Icc (-(R : ℝ)) (R : ℝ) := fun t ht => ht.1.2
    have hfin : volume (S_trunc R) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono hsub_box)
    have hIR_ord : (I ∩ Icc (-(R : ℝ)) (R : ℝ)).OrdConnected := hI.inter ordConnected_Icc
    have htoReal := polya_lagrange_bounded_sublevel_le hk hIR_ord
      (hF.mono inter_subset_left) hc hε (fun t ht => hderiv t ht.1) hfin
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal htoReal
  have henn : volume {t ∈ I | |F 0 t| ≤ ε} ≤ ENNReal.ofReal B := by
    rw [← hunion, hmono.measure_iUnion]
    exact iSup_le htrunc_le
  exact ⟨henn, ENNReal.toReal_le_of_le_ofReal hB_nn henn⟩

/-- Reusable abstract `1`D-slice-to-product-Gaussian Fubini bound over `{ι : Type*}`. -/
theorem gaussian_pi_le_of_fiber_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {E : Set (ι → ℝ)} (hE : MeasurableSet E) {B : ℝ} (hB : 0 ≤ B)
    (h1d : ∀ y : ι → ℝ,
      (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ E} ≤ ENNReal.ofReal B) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real E ≤ B := by
  let γ := gaussianReal 0 1
  let γ_pi := Measure.pi fun _ : ι => γ
  let p_i₀ : ι → Prop := fun i => i = i₀
  let e_split := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p_i₀
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => γ) p_i₀
  let μ_one := @Measure.pi (Subtype p_i₀) (fun _ => ℝ) (Subtype.fintype p_i₀) _ (fun _ => γ)
  let μ_rest := @Measure.pi {i : ι // ¬ p_i₀ i} (fun _ => ℝ)
    (Subtype.fintype fun i => ¬ p_i₀ i) _ (fun _ => γ)
  have hE_eq : γ_pi E = (μ_one.prod μ_rest) (e_split.symm ⁻¹' E) := by
    rw [← hmp.measure_preimage (e_split.symm.measurable hE).nullMeasurableSet]
    congr 1; ext x; change x ∈ E ↔ e_split.symm (e_split x) ∈ E
    rw [e_split.symm_apply_apply]
  have hprod_eval : (μ_one.prod μ_rest) (e_split.symm ⁻¹' E) =
      ∫⁻ z, μ_one {w : Subtype p_i₀ → ℝ | e_split.symm (w, z) ∈ E} ∂μ_rest :=
    Measure.prod_apply_symm (e_split.symm.measurable hE)
  let j₀ : Subtype p_i₀ := ⟨i₀, rfl⟩
  have huniq : ∀ u : Subtype p_i₀, u = j₀ := fun ⟨j, hj⟩ => Subtype.ext hj
  have hsec_le (z : {i : ι // ¬ p_i₀ i} → ℝ) :
      μ_one {w : Subtype p_i₀ → ℝ | e_split.symm (w, z) ∈ E} ≤ ENNReal.ofReal B := by
    let y : ι → ℝ := e_split.symm (0, z)
    have hupd_eq (w : Subtype p_i₀ → ℝ) :
        e_split.symm (w, z) = Function.update y i₀ (w j₀) := by
      funext i
      by_cases hi : i = i₀
      · subst hi; simp [e_split, y, j₀, p_i₀, MeasurableEquiv.piEquivPiSubtypeProd]
      · simp [e_split, y, hi, p_i₀, MeasurableEquiv.piEquivPiSubtypeProd]
    have hset_eq : {w : Subtype p_i₀ → ℝ | e_split.symm (w, z) ∈ E} =
        Set.univ.pi (fun _ : Subtype p_i₀ => {t : ℝ | Function.update y i₀ t ∈ E}) := by
      ext w
      simp only [mem_setOf_eq, mem_univ_pi, hupd_eq]
      exact ⟨fun hw u => huniq u ▸ hw, fun hw => hw j₀⟩
    rw [hset_eq]
    have hpi : μ_one (Set.univ.pi fun _ : Subtype p_i₀ => {t : ℝ | Function.update y i₀ t ∈ E}) =
        γ {t : ℝ | Function.update y i₀ t ∈ E} := by
      dsimp only [μ_one]
      rw [@Measure.pi_pi (Subtype p_i₀) (fun _ => ℝ) (Subtype.fintype p_i₀) _ (fun _ => γ)]
      refine Finset.prod_eq_single j₀ ?_ ?_
      · rintro ⟨j, hj⟩ _ hne; exact (hne (Subtype.ext hj)).elim
      · intro h; exact (h (@Finset.mem_univ (Subtype p_i₀) (Subtype.fintype p_i₀) j₀)).elim
    rw [hpi]; exact h1d y
  have htot : γ_pi E ≤ ENNReal.ofReal B := by
    rw [hE_eq, hprod_eval]
    refine (lintegral_mono hsec_le).trans ?_
    haveI : IsProbabilityMeasure μ_rest := by dsimp only [μ_rest]; infer_instance
    rw [lintegral_const, measure_univ, mul_one]
  rw [Measure.real]
  exact ENNReal.toReal_le_of_le_ofReal hB htot

private theorem gaussianReal_le_inv_sqrt_two_pi_vol_hd (S : Set ℝ) :
    (gaussianReal 0 1) S ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume S := by
  rw [gaussianReal_apply 0 (by norm_num) S, ← setLIntegral_const]
  refine setLIntegral_mono_ae (by fun_prop) ?_
  filter_upwards with t _
  rw [gaussianPDF]
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t]))

/-- Piecewise higher-derivative product-Gaussian micro-band anti-concentration: if each coordinate
`i₀` fiber of `Ω` is covered by `M` `OrdConnected` pieces on which `F` admits an order-`k_m`
derivative chain with `|G_{m, k_m}| ≥ c > 0`, then
`ℙ(x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)) ≤ ∑ m : Fin M, (4 * k_m / √(2 π)) * (δ / (2 * c)) ^ (1 / k_m)`. -/
theorem gaussian_higherDeriv_piecewise_anticoncentration
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (hΩ : MeasurableSet Ω)
    {M : ℕ} (k : Fin M → ℕ) (hk : ∀ m, 1 ≤ k m)
    {c e₀ δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hfib : ∀ y : ι → ℝ, ∃ (I_piece : Fin M → Set ℝ) (G : Fin M → ℕ → ℝ → ℝ),
      {t : ℝ | Function.update y i₀ t ∈ Ω} ⊆ ⋃ m : Fin M, I_piece m ∧
      ∀ m : Fin M, (I_piece m).OrdConnected ∧
        KleinbockMargulis.IsDerivChain (k m) (G m) (I_piece m) ∧
        (∀ t ∈ I_piece m, G m 0 t = F (Function.update y i₀ t)) ∧
        (∀ t ∈ I_piece m, c ≤ |G m (k m) t|)) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      ∑ m : Fin M, (4 * (k m : ℝ) / Real.sqrt (2 * Real.pi)) *
        (δ / (2 * c)) ^ ((k m : ℝ)⁻¹) := by
  let B_m : Fin M → ℝ := fun m =>
    (4 * (k m : ℝ) / Real.sqrt (2 * Real.pi)) * (δ / (2 * c)) ^ ((k m : ℝ)⁻¹)
  have hBm_nn (m : Fin M) : 0 ≤ B_m m := by
    dsimp [B_m]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg hδ (by positivity)) _)
  have hB_nn : 0 ≤ ∑ m : Fin M, B_m m := Finset.sum_nonneg fun m _ => hBm_nn m
  refine gaussian_pi_le_of_fiber_bound i₀ (hΩ.inter (hF measurableSet_Ioc)) hB_nn fun y => ?_
  obtain ⟨I_piece, G, hcov, hpiece⟩ := hfib y
  let mid : ℝ := e₀ + δ / 2
  have hpiece_le (m : Fin M) :
      (gaussianReal 0 1) {t ∈ I_piece m | F (Function.update y i₀ t) ∈ Ioc e₀ (e₀ + δ)} ≤
        ENNReal.ofReal (B_m m) := by
    obtain ⟨hord, hchain, hG0, hGderiv⟩ := hpiece m
    let G_shift : ℕ → ℝ → ℝ := fun j t => if j = 0 then G m 0 t - mid else G m j t
    have hchain_shift : KleinbockMargulis.IsDerivChain (k m) G_shift (I_piece m) := by
      intro j hj t ht
      have hbase := hchain j hj t ht
      by_cases hj0 : j = 0
      · subst hj0
        simpa only [G_shift, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false] using
          hbase.sub_const mid
      · have hj1 : j + 1 ≠ 0 := Nat.succ_ne_zero j
        simpa only [G_shift, hj0, hj1, ↓reduceIte] using hbase
    have hkm_ne0 : k m ≠ 0 := Nat.pos_iff_ne_zero.mp (hk m)
    have hderiv_shift : ∀ t ∈ I_piece m, c ≤ |G_shift (k m) t| := fun t ht => by
      simpa only [G_shift, hkm_ne0, ↓reduceIte] using hGderiv t ht
    have hsub : {t ∈ I_piece m | F (Function.update y i₀ t) ∈ Ioc e₀ (e₀ + δ)} ⊆
        {t ∈ I_piece m | |G_shift 0 t| ≤ δ / 2} := by
      rintro t ⟨htI, hlo, hhi⟩
      refine ⟨htI, ?_⟩
      simp only [G_shift, ↓reduceIte, hG0 t htI, mid]
      exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
    have hvol := (polya_lagrange_derivChain_sublevel_le (hk m) hord hchain_shift hc
      (half_nonneg hδ) hderiv_shift).1
    have hdiv_eq : (δ / 2) / c = δ / (2 * c) := by ring
    rw [hdiv_eq] at hvol
    calc (gaussianReal 0 1) {t ∈ I_piece m | F (Function.update y i₀ t) ∈ Ioc e₀ (e₀ + δ)}
        ≤ (gaussianReal 0 1) {t ∈ I_piece m | |G_shift 0 t| ≤ δ / 2} := measure_mono hsub
      _ ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) *
            volume {t ∈ I_piece m | |G_shift 0 t| ≤ δ / 2} :=
          gaussianReal_le_inv_sqrt_two_pi_vol_hd _
      _ ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) *
            ENNReal.ofReal (4 * (k m : ℝ) * (δ / (2 * c)) ^ ((k m : ℝ)⁻¹)) :=
          mul_le_mul_right hvol _
      _ = ENNReal.ofReal (B_m m) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; dsimp [B_m]; ring
  have hcov_E : {t : ℝ | Function.update y i₀ t ∈ {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)}} ⊆
      ⋃ m : Fin M, {t ∈ I_piece m | F (Function.update y i₀ t) ∈ Ioc e₀ (e₀ + δ)} := by
    rintro t ⟨htΩ, htF⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hcov htΩ)
    exact mem_iUnion.mpr ⟨m, hm, htF⟩
  calc (gaussianReal 0 1) {t : ℝ | Function.update y i₀ t ∈ {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)}}
      ≤ (gaussianReal 0 1)
          (⋃ m : Fin M, {t ∈ I_piece m | F (Function.update y i₀ t) ∈ Ioc e₀ (e₀ + δ)}) :=
        measure_mono hcov_E
    _ ≤ ∑ m : Fin M,
          (gaussianReal 0 1) {t ∈ I_piece m | F (Function.update y i₀ t) ∈ Ioc e₀ (e₀ + δ)} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ m : Fin M, ENNReal.ofReal (B_m m) :=
        Finset.sum_le_sum fun m _ => hpiece_le m
    _ = ENNReal.ofReal (∑ m : Fin M, B_m m) :=
        (ENNReal.ofReal_sum_of_nonneg fun m _ => hBm_nn m).symm

/-- Single-budget order-`N` anti-concentration at quadratic scale `δ = 2^{-b N²}`:
whenever chart multiplicity satisfies `M ≤ 2^{γ N}` with `γ < b`, `(δ)^{1/N} = 2^{-b N}` beats
`M ≤ 2^{γ N}` with exponential decay `M * δ^{1/N} ≤ 2^{-(b - γ) N}`. -/
theorem order_N_exponential_anticoncentration_at_quadraticScale
    {N M : ℕ} (hN : 1 ≤ N) {b γ : ℝ} (hM : (M : ℝ) ≤ (2 : ℝ) ^ (γ * (N : ℝ))) :
    (M : ℝ) * ((2 : ℝ) ^ (-b * (N : ℝ) ^ 2)) ^ ((N : ℝ)⁻¹) ≤
      (2 : ℝ) ^ (-(b - γ) * (N : ℝ)) := by
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrpow : ((2 : ℝ) ^ (-b * (N : ℝ) ^ 2)) ^ ((N : ℝ)⁻¹) = (2 : ℝ) ^ (-b * (N : ℝ)) := by
    rw [← Real.rpow_mul two_pos.le]
    congr 1
    field_simp [hN_pos.ne']
  rw [hrpow]
  calc (M : ℝ) * (2 : ℝ) ^ (-b * (N : ℝ))
      ≤ (2 : ℝ) ^ (γ * (N : ℝ)) * (2 : ℝ) ^ (-b * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg two_pos.le _)
    _ = (2 : ℝ) ^ (-(b - γ) * (N : ℝ)) := by
        rw [← Real.rpow_add two_pos]
        congr 1; ring

/-- Sublinear-order (`1 ≤ k`) transfer across all `Q = (4 N + 1)(2 N + 2)(2^N)²` active circuit
budgets to fixed-`1 / 10` zero-drop locking `m_{1/10 + δ} = m_{1/10}`, together with the sharp
order-`N` active-budget barrier under the quadratic compiler cap `b ≤ N² / 25`. -/
theorem fixed_tenth_locking_of_higherDeriv_sublinearOrder
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {N : ℕ} (hN : 2 ≤ N)
    (H : (ι → ℝ) → selfAdjoint (Register N))
    (hH_meas : ∀ j : ℕ, Measurable fun x => criticalHeight (H x) j)
    {Ω : ℕ → Set (ι → ℝ)} (hΩ_meas : ∀ j, MeasurableSet (Ω j))
    (M k : ℕ) (hk : 1 ≤ k) {c δ : ℝ} (hc : 0 < c) (hδ : 0 ≤ δ)
    (hfib : ∀ j < (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2, ∀ y : ι → ℝ,
      ∃ (I_piece : Fin M → Set ℝ) (G : Fin M → ℕ → ℝ → ℝ),
        {t : ℝ | Function.update y i₀ t ∈ Ω j} ⊆ ⋃ m : Fin M, I_piece m ∧
        ∀ m : Fin M, (I_piece m).OrdConnected ∧
          KleinbockMargulis.IsDerivChain k (G m) (I_piece m) ∧
          (∀ t ∈ I_piece m, G m 0 t = criticalHeight (H (Function.update y i₀ t)) j) ∧
          (∀ t ∈ I_piece m, c ≤ |G m k t|)) :
    let Q := (4 * N + 1) * (2 * N + 2) * (2 ^ N) ^ 2
    let Ω_all := ⋂ j ∈ Finset.range Q, Ω j
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω_all | ∃ m₁ m₂ : ℕ,
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
        IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂} ≤
      (Q : ℝ) * ((M : ℝ) * (4 * (k : ℝ) / Real.sqrt (2 * Real.pi)) *
        (δ / (2 * c)) ^ ((k : ℝ)⁻¹)) := by
  intro Q Ω_all
  let γ_pi := Measure.pi fun _ : ι => gaussianReal 0 1
  haveI : IsProbabilityMeasure γ_pi := by dsimp only [γ_pi]; infer_instance
  let Bad := {x : ι → ℝ | x ∈ Ω_all ∧ ∃ m₁ m₂ : ℕ,
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10) m₁ ∧
    IsRecurrentOrbitCircuitMaximumAt (H x) (1 / 10 + δ) m₂ ∧ m₁ ≠ m₂}
  have hsub : Bad ⊆ ⋃ j ∈ Finset.range Q,
      {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} := by
    rintro x ⟨hxΩ, m₁, m₂, hm₁, hm₂, hne⟩
    have hnot_clear : ¬ (1 / 10 : ℝ) ∉ jumpTolerances (H x) δ := fun hclear =>
      hne ((maximum_eq_iff_criticalHeight_clearance hN (H x) (by norm_num) hδ hm₁ hm₂).2.mpr hclear)
    rw [not_not] at hnot_clear
    obtain ⟨j, _, hj_mem⟩ := hnot_clear
    have hj_lt_Q : j < Q := by
      by_contra hge
      have h0 := criticalHeight_eq_zero_of_exact_cap hN (H x) (Nat.le_of_not_lt hge)
      rw [h0] at hj_mem; linarith only [hj_mem.1]
    exact mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hj_lt_Q,
      (mem_iInter₂.mp hxΩ) j (Finset.mem_range.mpr hj_lt_Q), hj_mem⟩
  calc γ_pi.real Bad
      ≤ γ_pi.real (⋃ j ∈ Finset.range Q,
          {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)}) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range Q,
          γ_pi.real {x ∈ Ω j | criticalHeight (H x) j ∈ Ioc (1 / 10) (1 / 10 + δ)} :=
          measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range Q,
          (M : ℝ) * (4 * (k : ℝ) / Real.sqrt (2 * Real.pi)) * (δ / (2 * c)) ^ ((k : ℝ)⁻¹) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h1 := gaussian_higherDeriv_piecewise_anticoncentration i₀ (hH_meas j) (hΩ_meas j)
            (fun _ : Fin M => k) (fun _ => hk) hc hδ (hfib j (Finset.mem_range.mp hj))
          simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_assoc] using h1
    _ = (Q : ℝ) * ((M : ℝ) * (4 * (k : ℝ) / Real.sqrt (2 * Real.pi)) *
          (δ / (2 * c)) ^ ((k : ℝ)⁻¹)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Sharp active-budget threshold at order `k = N` vs. sublinear order `3 N k ≤ b`:
1. If `1 ≤ k` and `3 * N * k ≤ b`, then `(4 : ℝ) ^ N * ((2 : ℝ) ^ (-b : ℝ)) ^ (1 / k) ≤ 2 ^ (-N)`.
2. Under the `binary_compiler_envelope` quadratic-precision constraint `(b : ℝ) ≤ N² / 25` (`1 ≤ N`),
   order-`N` root extraction `((2 : ℝ) ^ (-b : ℝ)) ^ (1 / N)` satisfies
   `(2 : ℝ) ^ ((49 / 25) * N) ≤ (4 : ℝ) ^ N * ((2 : ℝ) ^ (-b : ℝ)) ^ (1 / N)` and hence cannot
   absorb the `4^N` active circuit budgets. -/
theorem activeBudget_union_order_threshold {N b k : ℕ} (hN : 1 ≤ N) :
    (1 ≤ k → 3 * N * k ≤ b →
      (4 : ℝ) ^ N * (((2 : ℝ) ^ (-(b : ℝ))) ^ ((k : ℝ)⁻¹)) ≤ (2 : ℝ) ^ (-(N : ℝ))) ∧
    ((b : ℝ) ≤ (N : ℝ) ^ 2 / 25 →
      (2 : ℝ) ^ ((49 / 25 : ℝ) * (N : ℝ)) ≤
        (4 : ℝ) ^ N * (((2 : ℝ) ^ (-(b : ℝ))) ^ ((N : ℝ)⁻¹))) := by
  have h4N : (4 : ℝ) ^ N = (2 : ℝ) ^ (2 * (N : ℝ)) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, ← pow_mul, ← Real.rpow_natCast]
    push_cast; rfl
  refine ⟨fun hk h3 => ?_, fun hcap => ?_⟩
  · have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hdiv : -(b : ℝ) * (k : ℝ)⁻¹ ≤ -3 * (N : ℝ) := by
      rw [← div_eq_mul_inv, div_le_iff₀ hk_pos]
      have hreal : 3 * (N : ℝ) * (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast h3
      linarith only [hreal]
    rw [h4N, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only [hdiv])
  · have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hdiv : -(N : ℝ) / 25 ≤ -(b : ℝ) * (N : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff_of_pos_right hN_pos]
      have h1 : -(N : ℝ) / 25 * (N : ℝ) = -((N : ℝ) ^ 2 / 25) := by ring
      linarith only [hcap, h1]
    rw [h4N, ← Real.rpow_mul two_pos.le, ← Real.rpow_add two_pos]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith only [hdiv])

/-! ## Section 2: Higher-order unitary-jet Danskin (`s = u^m`) and Hölder-Dini collar bounds -/

/-- Abstract `C*`-algebra `m`-th unitary-jet self-adjointness: if `V : ℝ → A` takes unitary values
for `u ≥ 0` and satisfies `‖V(u) - (V(0) + u^m • M_m)‖ / u^m → 0` as `u → 0⁺` (`m ≥ 1`), then
`K_m := i • (M_m * star (V 0))` is self-adjoint (`star K_m = K_m`). -/
theorem unitaryJet_isSelfAdjoint {A : Type*} [CStarAlgebra A] {m : ℕ} (hm : 1 ≤ m)
    {V : ℝ → A} {M_m : A}
    (hV_unit : ∀ u : ℝ, 0 ≤ u → V u ∈ unitary A)
    (hjet : Tendsto (fun u : ℝ => ‖V u - (V 0 + ((u ^ m : ℝ) : ℂ) • M_m)‖ / u ^ m)
      (𝓝[>] 0) (𝓝 0)) :
    IsSelfAdjoint (Complex.I • (M_m * star (V 0))) := by
  let S_skew : A := M_m * star (V 0) + V 0 * star M_m
  suffices hS0 : S_skew = 0 by
    rw [IsSelfAdjoint, star_smul, star_mul, star_star, Complex.star_def, Complex.conj_I, neg_smul]
    have hneg : -(V 0 * star M_m) = M_m * star (V 0) := by
      have h1 := eq_neg_of_add_eq_zero_right hS0
      rw [← neg_eq_iff_eq_neg] at h1
      exact h1
    rw [← smul_neg, hneg]
  have h0_unit : V 0 * star (V 0) = 1 := (Unitary.mem_iff.mp (hV_unit 0 le_rfl)).2
  have hV0_norm : ‖V 0‖ ≤ 1 := (CStarRing.norm_of_mem_unitary (hV_unit 0 le_rfl)).le
  let R : ℝ → A := fun u => V u - (V 0 + ((u ^ m : ℝ) : ℂ) • M_m)
  have hbound : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      ‖S_skew‖ ≤ u ^ m * ‖M_m‖ ^ 2 + (‖R u‖ / u ^ m) +
        (1 + u ^ m * ‖M_m‖) * (‖R u‖ / u ^ m) := by
    filter_upwards [self_mem_nhdsWithin] with u hu_pos
    have hu : 0 < u := hu_pos
    have hum_pos : 0 < u ^ m := pow_pos hu m
    have hu_unit : V u * star (V u) = 1 := (Unitary.mem_iff.mp (hV_unit u hu.le)).2
    have hstVu_norm : ‖star (V u)‖ ≤ 1 := by
      rw [norm_star]; exact (CStarRing.norm_of_mem_unitary (hV_unit u hu.le)).le
    have hVu_decomp : V u = (V 0 + ((u ^ m : ℝ) : ℂ) • M_m) + R u := by dsimp [R]; abel
    have hid : ((u ^ m : ℝ) : ℂ) • S_skew =
        -(R u * star (V u) + (V 0 + ((u ^ m : ℝ) : ℂ) • M_m) * star (R u) +
          (((u ^ m : ℝ) * (u ^ m : ℝ) : ℝ) : ℂ) • (M_m * star M_m)) := by
      have hexp : V u * star (V u) =
          V 0 * star (V 0) + ((u ^ m : ℝ) : ℂ) • S_skew +
            (R u * star (V u) + (V 0 + ((u ^ m : ℝ) : ℂ) • M_m) * star (R u) +
              (((u ^ m : ℝ) * (u ^ m : ℝ) : ℝ) : ℂ) • (M_m * star M_m)) := by
        conv_lhs => arg 1; rw [hVu_decomp]
        rw [add_mul]
        conv_lhs => arg 1; arg 2; rw [hVu_decomp]
        rw [star_add, mul_add, star_add, add_mul, add_mul, mul_add, mul_add,
          star_smul, Complex.star_def, Complex.conj_ofReal]
        simp only [S_skew, smul_add, mul_smul_comm, smul_mul_assoc, smul_smul, Complex.ofReal_mul]
        abel
      rw [hu_unit, h0_unit] at hexp
      have hsum0 : ((u ^ m : ℝ) : ℂ) • S_skew +
          (R u * star (V u) + (V 0 + ((u ^ m : ℝ) : ℂ) • M_m) * star (R u) +
            (((u ^ m : ℝ) * (u ^ m : ℝ) : ℝ) : ℂ) • (M_m * star M_m)) = 0 := by
        have h := congrArg (fun X : A => X - 1) hexp
        simpa [add_assoc, add_comm, add_left_comm] using h.symm
      exact eq_neg_of_add_eq_zero_left hsum0
    have hnorm_smul : u ^ m * ‖S_skew‖ = ‖((u ^ m : ℝ) : ℂ) • S_skew‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hum_pos.le]
    have h1 : ‖R u * star (V u)‖ ≤ ‖R u‖ :=
      (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hstVu_norm (norm_nonneg _)).trans_eq (mul_one _))
    have h2 : ‖(V 0 + ((u ^ m : ℝ) : ℂ) • M_m) * star (R u)‖ ≤
        (1 + u ^ m * ‖M_m‖) * ‖R u‖ := by
      calc ‖(V 0 + ((u ^ m : ℝ) : ℂ) • M_m) * star (R u)‖
          ≤ ‖V 0 + ((u ^ m : ℝ) : ℂ) • M_m‖ * ‖star (R u)‖ := norm_mul_le _ _
        _ = ‖V 0 + ((u ^ m : ℝ) : ℂ) • M_m‖ * ‖R u‖ := by rw [norm_star]
        _ ≤ (1 + u ^ m * ‖M_m‖) * ‖R u‖ := by
            refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (norm_nonneg _)
            rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hum_pos.le]
            exact add_le_add_right hV0_norm _
    have h3 : ‖(((u ^ m : ℝ) * (u ^ m : ℝ) : ℝ) : ℂ) • (M_m * star M_m)‖ ≤
        (u ^ m) ^ 2 * ‖M_m‖ ^ 2 := by
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hum_pos.le hum_pos.le), ← sq]
      exact mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans_eq (by rw [norm_star, sq])) (sq_nonneg _)
    have htot_mul : u ^ m * ‖S_skew‖ ≤
        (u ^ m) ^ 2 * ‖M_m‖ ^ 2 + ‖R u‖ + (1 + u ^ m * ‖M_m‖) * ‖R u‖ := by
      rw [hnorm_smul, hid, norm_neg]
      have htri := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      linarith only [htri, h1, h2, h3]
    rw [← le_div_iff₀' hum_pos] at htot_mul
    refine htot_mul.trans_eq ?_
    field_simp [hum_pos.ne']
  have hpow0 : Tendsto (fun u : ℝ => u ^ m) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun u : ℝ => u ^ m) := continuous_pow m
    simpa only [zero_pow (Nat.pos_iff_ne_zero.mp hm)] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hrhs_tend : Tendsto (fun u : ℝ =>
      u ^ m * ‖M_m‖ ^ 2 + (‖R u‖ / u ^ m) + (1 + u ^ m * ‖M_m‖) * (‖R u‖ / u ^ m))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := hpow0.mul_const (‖M_m‖ ^ 2)
    have h2 : Tendsto (fun u : ℝ => 1 + u ^ m * ‖M_m‖) (𝓝[>] 0) (𝓝 1) := by
      simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hpow0.mul_const ‖M_m‖)
    simpa only [zero_mul, mul_zero, add_zero] using (h1.add hjet).add (h2.mul hjet)
  have hle0 : ‖S_skew‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hrhs_tend hbound
  exact norm_le_zero_iff.mp hle0

private theorem abs_torusCriticalHeight_sub_le {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (V₁ V₂ : UGroup N) (j : ℕ) :
    |torusCriticalHeight e V₁ j - torusCriticalHeight e V₂ j| ≤ 2 * ‖V₁.val - V₂.val‖ := by
  have hpt_le (W₁ W₂ : UGroup N) (θ : Fin d → UnitAddCircle) :
      Metric.infDist (projectiveSpectralMatrix e W₁ θ) (phaseCircuitMatrixImageAtMost N j) ≤
        torusCriticalHeight e W₂ j + 2 * ‖W₁.val - W₂.val‖ := by
    let D_θ : Register N :=
      Matrix.diagonal (fun q => fourier 1 (RHTower.zeroAnchoredPhase d θ (e q)))
    have hD_unit : D_θ ∈ unitary (Register N) := by
      rw [Unitary.mem_iff, star_eq_conjTranspose, diagonal_conjTranspose,
        diagonal_mul_diagonal, diagonal_mul_diagonal]
      constructor <;> ext a b <;> by_cases hab : a = b
      · subst hab; simp only [diagonal_apply_eq, one_apply_eq]
        exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
      · simp [hab]
      · subst hab; simp only [diagonal_apply_eq, one_apply_eq]; rw [mul_comm]
        exact Complex.normSq_eq_conj_mul_self.symm.trans (by simp)
      · simp [hab]
    have hD_norm : ‖D_θ‖ ≤ 1 := (CStarRing.norm_of_mem_unitary hD_unit).le
    have hW1_st : ‖(W₁⁻¹ : UGroup N).val‖ ≤ 1 :=
      (CStarRing.norm_of_mem_unitary (W₁⁻¹ : UGroup N).2).le
    have hW2_n : ‖W₂.val‖ ≤ 1 := (CStarRing.norm_of_mem_unitary W₂.2).le
    have hdiff_spec : ‖projectiveSpectralMatrix e W₁ θ - projectiveSpectralMatrix e W₂ θ‖ ≤
        2 * ‖W₁.val - W₂.val‖ := by
      unfold projectiveSpectralMatrix
      have hinv1 : (W₁⁻¹ : UGroup N).val = star W₁.val := rfl
      have hinv2 : (W₂⁻¹ : UGroup N).val = star W₂.val := rfl
      have hsplit : W₁.val * D_θ * (W₁⁻¹ : UGroup N).val - W₂.val * D_θ * (W₂⁻¹ : UGroup N).val =
          (W₁.val - W₂.val) * D_θ * (W₁⁻¹ : UGroup N).val +
            W₂.val * D_θ * star (W₁.val - W₂.val) := by
        rw [hinv1, hinv2, star_sub]; noncomm_ring
      rw [hsplit]
      have ha : ‖(W₁.val - W₂.val) * D_θ * (W₁⁻¹ : UGroup N).val‖ ≤ ‖W₁.val - W₂.val‖ := by
        calc _ ≤ ‖(W₁.val - W₂.val) * D_θ‖ * ‖(W₁⁻¹ : UGroup N).val‖ := norm_mul_le _ _
          _ ≤ (‖W₁.val - W₂.val‖ * 1) * 1 := mul_le_mul
              ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _)))
              hW1_st (norm_nonneg _) (by positivity)
          _ = ‖W₁.val - W₂.val‖ := by ring
      have hb : ‖W₂.val * D_θ * star (W₁.val - W₂.val)‖ ≤ ‖W₁.val - W₂.val‖ := by
        calc _ ≤ ‖W₂.val * D_θ‖ * ‖star (W₁.val - W₂.val)‖ := norm_mul_le _ _
          _ ≤ (1 * 1) * ‖W₁.val - W₂.val‖ := mul_le_mul
              ((norm_mul_le _ _).trans (mul_le_mul hW2_n hD_norm (norm_nonneg _) zero_le_one))
              (norm_star _).le (norm_nonneg _) zero_le_one
          _ = ‖W₁.val - W₂.val‖ := by ring
      exact (norm_add_le _ _).trans (by linarith only [ha, hb])
    have hinf_tri : Metric.infDist (projectiveSpectralMatrix e W₁ θ)
        (phaseCircuitMatrixImageAtMost N j) ≤
        Metric.infDist (projectiveSpectralMatrix e W₂ θ) (phaseCircuitMatrixImageAtMost N j) +
          dist (projectiveSpectralMatrix e W₁ θ) (projectiveSpectralMatrix e W₂ θ) :=
      Metric.infDist_le_infDist_add_dist
    have hle_sup : Metric.infDist (projectiveSpectralMatrix e W₂ θ)
        (phaseCircuitMatrixImageAtMost N j) ≤ torusCriticalHeight e W₂ j := by
      unfold torusCriticalHeight
      refine le_csSup ⟨2, ?_⟩ (mem_range_self θ)
      rintro _ ⟨θ', rfl⟩
      have h1 : (1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N) ∈
          phaseCircuitMatrixImageAtMost N j :=
        mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩
      refine (Metric.infDist_le_dist_of_mem h1).trans ?_
      rw [dist_eq_norm, one_smul, TwoQubitCircuit.one_eval]
      exact (norm_sub_le _ _).trans (by
        have hu1 := CStarRing.norm_of_mem_unitary (projectiveSpectralMatrix_mem_unitary e W₂ θ')
        have hu2 : ‖(1 : Register N)‖ = 1 :=
          CStarRing.norm_of_mem_unitary (Unitary.mem_iff.mpr ⟨by simp, by simp⟩)
        linarith only [hu1, hu2])
    rw [dist_eq_norm] at hinf_tri
    linarith only [hinf_tri, hle_sup, hdiff_spec]
  have hsup_le (W₁ W₂ : UGroup N) :
      torusCriticalHeight e W₁ j ≤ torusCriticalHeight e W₂ j + 2 * ‖W₁.val - W₂.val‖ := by
    unfold torusCriticalHeight
    refine csSup_le (range_nonempty _) ?_
    rintro _ ⟨θ, rfl⟩
    exact hpt_le W₁ W₂ θ
  have h1 := hsup_le V₁ V₂
  have h2 := hsup_le V₂ V₁
  rw [norm_sub_rev V₂.val V₁.val] at h2
  exact abs_le.mpr ⟨by linarith only [h2], by linarith only [h1]⟩

/-- Higher-order unitary-jet Danskin lower Dini envelope theorem (`s = u^m`) without `C_j` nets:
if `V : ℝ → UGroup N` satisfies `‖V(u) - (V(0) + u^m • M_m)‖ / u^m → 0` as `u → 0⁺` (`m ≥ 1`),
then `K_m := ⟨i • (M_m * star V(0)), _⟩` governs the reparameterized `s = u^m` right Dini slope of
`s ↦ torusCriticalHeight e (V (s ^ (1 / m))) j` at any maximizing phase point `θ_⋆`. -/
theorem liminf_torusCriticalHeight_higherOrderUnitaryJet_ge {N d m : ℕ} (hm : 1 ≤ m)
    (e : Config N ≃ Fin (d + 1)) (V : ℝ → UGroup N) (M_m : Register N)
    (hjet : Tendsto (fun u : ℝ => ‖(V u).val - ((V 0).val + ((u ^ m : ℝ) : ℂ) • M_m)‖ / u ^ m)
      (𝓝[>] 0) (𝓝 0))
    (j : ℕ) (θ_star : Fin d → UnitAddCircle)
    (hmax : torusCriticalHeight e (V 0) j =
      Metric.infDist (projectiveSpectralMatrix e (V 0) θ_star) (phaseCircuitMatrixImageAtMost N j))
    (hr : 0 < torusCriticalHeight e (V 0) j) :
    let hKm : IsSelfAdjoint (Complex.I • (M_m * star (V 0).val)) :=
      unitaryJet_isSelfAdjoint hm (fun u _ => (V u).2) hjet
    let K_m : selfAdjoint (Register N) := ⟨Complex.I • (M_m * star (V 0).val), hKm⟩
    let U₀ := projectiveSpectralMatrix e (V 0) θ_star
    let r := torusCriticalHeight e (V 0) j
    let W_opt := {W ∈ phaseCircuitMatrixImageAtMost N j | ‖U₀ - W‖ = r}
    ∀ ε > 0, ∀ᶠ s in 𝓝[>] 0,
      ∃ W_star ∈ W_opt, ∃ ψ_star ∈ maxRightSingularSphere (U₀ - W_star),
        -(inner ℂ (matAct W_star ψ_star) (matAct (K_m.val * U₀ - U₀ * K_m.val) ψ_star)).im / r - ε <
          (torusCriticalHeight e (V (s ^ ((m : ℝ)⁻¹))) j - r) / s := by
  intro hKm K_m U₀ r W_opt ε hε
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  -- Map `s ↦ s ^ (1 / m)` sends `𝓝[>] 0` to `𝓝[>] 0`!
  have hroot_tend : Tendsto (fun s : ℝ => s ^ ((m : ℝ)⁻¹)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : ContinuousAt (fun s : ℝ => s ^ ((m : ℝ)⁻¹)) 0 :=
        Real.continuousAt_rpow_const 0 _ (Or.inr (inv_pos.mpr hm_pos).le)
      simpa only [Real.zero_rpow (inv_ne_zero hm_pos.ne')] using
        hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.rpow_pos_of_pos hs _
  -- Compare `V (s ^ (1/m))` with `transverseEigenspaceFlow K_m (V 0) s` at order `o(s)`!
  have hflow_diff : Tendsto (fun s : ℝ =>
      ‖(V (s ^ ((m : ℝ)⁻¹))).val - (transverseEigenspaceFlow K_m (V 0) s).val‖ / s)
      (𝓝[>] 0) (𝓝 0) := by
    have hjet_s := hjet.comp hroot_tend
    have hexp_rem : Tendsto (fun s : ℝ =>
        ‖((V 0).val + (s : ℂ) • M_m) - (transverseEigenspaceFlow K_m (V 0) s).val‖ / s)
        (𝓝[>] 0) (𝓝 0) := by
      have hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ),
          ‖((V 0).val + (s : ℂ) • M_m) - (transverseEigenspaceFlow K_m (V 0) s).val‖ / s ≤
            (s / 2) * ‖K_m.val‖ ^ 2 := by
        filter_upwards [self_mem_nhdsWithin] with s hs_pos
        have hs : 0 < s := hs_pos
        have hM_eq : M_m = (-Complex.I) • (K_m.val * (V 0).val) := by
          dsimp [K_m]
          rw [smul_mul_assoc, mul_assoc, (Unitary.mem_iff.mp (V 0).2).1, mul_one, smul_smul,
            show (-Complex.I) * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]
        have hlin : (V 0).val + (s : ℂ) • M_m =
            (1 + (s : ℂ) • ((-Complex.I) • K_m.val)) * (V 0).val := by
          rw [hM_eq, add_mul, one_mul, smul_mul_assoc]
        have hfl : (transverseEigenspaceFlow K_m (V 0) s).val =
            unitaryEvolution K_m.val s * (V 0).val := rfl
        have hV0_n : ‖(V 0).val‖ ≤ 1 := (CStarRing.norm_of_mem_unitary (V 0).2).le
        have htay := norm_selfAdjoint_exp_sub_hamiltonianTaylor_le K_m.val K_m.2 1 s
        have htay1 : selfAdjointHamiltonianTaylor K_m.val 1 s =
            1 + (s : ℂ) • ((-Complex.I) • K_m.val) := by
          simp [selfAdjointHamiltonianTaylor, cstarExponentialTaylor, Finset.sum_range_succ,
            Complex.real_smul, smul_smul]
        rw [hlin, hfl, ← sub_mul, norm_sub_rev]
        have hmul_le : ‖(unitaryEvolution K_m.val s - (1 + (s : ℂ) • ((-Complex.I) • K_m.val))) *
            (V 0).val‖ ≤ ‖K_m.val‖ ^ 2 * |s| ^ 2 / 2 := by
          calc _ ≤ ‖unitaryEvolution K_m.val s - (1 + (s : ℂ) • ((-Complex.I) • K_m.val))‖ *
                ‖(V 0).val‖ := norm_mul_le _ _
            _ ≤ ‖unitaryEvolution K_m.val s - (1 + (s : ℂ) • ((-Complex.I) • K_m.val))‖ * 1 :=
                mul_le_mul_of_nonneg_left hV0_n (norm_nonneg _)
            _ ≤ ‖K_m.val‖ ^ 2 * |s| ^ 2 / 2 := by
                rw [mul_one, ← htay1]
                simpa [unitaryEvolution, Nat.factorial] using htay
        rw [abs_of_pos hs, div_le_iff₀ hs]
        have h1 : (s / 2) * ‖K_m.val‖ ^ 2 * s = ‖K_m.val‖ ^ 2 * s ^ 2 / 2 := by ring
        linarith only [hmul_le, h1]
      have hlin0 : Tendsto (fun s : ℝ => (s / 2) * ‖K_m.val‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have hc : Continuous (fun s : ℝ => (s / 2) * ‖K_m.val‖ ^ 2) := by fun_prop
        simpa only [zero_div, zero_mul] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      refine squeeze_zero' ?_ hbound hlin0
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact div_nonneg (norm_nonneg _) (le_of_lt hs)
    have htri_s : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        ‖(V (s ^ ((m : ℝ)⁻¹))).val - (transverseEigenspaceFlow K_m (V 0) s).val‖ / s ≤
          ‖(V (s ^ ((m : ℝ)⁻¹))).val -
            ((V 0).val + (((s ^ ((m : ℝ)⁻¹)) ^ m : ℝ) : ℂ) • M_m)‖ / (s ^ ((m : ℝ)⁻¹)) ^ m +
          ‖((V 0).val + (s : ℂ) • M_m) - (transverseEigenspaceFlow K_m (V 0) s).val‖ / s := by
      filter_upwards [self_mem_nhdsWithin] with s hs_pos
      have hs : 0 < s := hs_pos
      have hpow_s : (s ^ ((m : ℝ)⁻¹)) ^ m = s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le, inv_mul_cancel₀ hm_pos.ne', Real.rpow_one]
      rw [hpow_s, ← add_div]
      refine div_le_div_of_nonneg_right ?_ hs.le
      have hsplit : (V (s ^ ((m : ℝ)⁻¹))).val - (transverseEigenspaceFlow K_m (V 0) s).val =
          ((V (s ^ ((m : ℝ)⁻¹))).val - ((V 0).val + (s : ℂ) • M_m)) +
            (((V 0).val + (s : ℂ) • M_m) - (transverseEigenspaceFlow K_m (V 0) s).val) := by
        abel
      rw [hsplit]
      exact norm_add_le _ _
    refine squeeze_zero' ?_ htri_s (by simpa only [add_zero] using hjet_s.add hexp_rem)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact div_nonneg (norm_nonneg _) (le_of_lt hs)
  have hbase := liminf_torusCriticalHeight_transverseFlow_ge e (V 0) K_m j θ_star hmax hr
    (ε / 2) (half_pos hε)
  have herr := (hflow_diff.const_mul 2).eventually_lt_const (half_pos hε)
  filter_upwards [self_mem_nhdsWithin, hbase, herr] with s hs_pos ⟨W_star, hW, ψ_star, hψ, hlt⟩ herr_s
  have hs : 0 < s := hs_pos
  have hlip := abs_torusCriticalHeight_sub_le e
    (V (s ^ ((m : ℝ)⁻¹))) (transverseEigenspaceFlow K_m (V 0) s) j
  have hquot_diff : |(torusCriticalHeight e (V (s ^ ((m : ℝ)⁻¹))) j - r) / s -
      (torusCriticalHeight e (transverseEigenspaceFlow K_m (V 0) s) j - r) / s| ≤
      2 * (‖(V (s ^ ((m : ℝ)⁻¹))).val - (transverseEigenspaceFlow K_m (V 0) s).val‖ / s) := by
    have hsub : (torusCriticalHeight e (V (s ^ ((m : ℝ)⁻¹))) j - r) / s -
        (torusCriticalHeight e (transverseEigenspaceFlow K_m (V 0) s) j - r) / s =
        (torusCriticalHeight e (V (s ^ ((m : ℝ)⁻¹))) j -
          torusCriticalHeight e (transverseEigenspaceFlow K_m (V 0) s) j) / s := by
      ring
    rw [hsub, abs_div, abs_of_pos hs, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hlip hs.le
  have hlow := (abs_le.mp hquot_diff).1
  refine ⟨W_star, hW, ψ_star, hψ, ?_⟩
  linarith only [hlt, hlow, herr_s]

private theorem add_pow_ge_pow_add_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∀ {m : ℕ}, 1 ≤ m → x ^ m + y ^ m ≤ (x + y) ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m _ ih =>
      have h1 : (x ^ m + y ^ m) * (x + y) ≤ (x + y) ^ (m + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right ih (by positivity)
      have h2 : x ^ (m + 1) + y ^ (m + 1) ≤ (x ^ m + y ^ m) * (x + y) := by
        have hid : (x ^ m + y ^ m) * (x + y) - (x ^ (m + 1) + y ^ (m + 1)) =
            x ^ m * y + y ^ m * x := by ring
        have hnn : 0 ≤ x ^ m * y + y ^ m * x := by positivity
        linarith only [hid, hnn]
      exact h2.trans h1

/-- Hölder-Dini collar diameter bound under `s = u^m` reparameterization: if `g` is continuous on
`Icc 0 R` (`0 ≤ R`, `m ≥ 1`) and `s ↦ g (s ^ (1 / m))` has right Dini slope `≥ c_m > 0` inside
`Ioo (a_band - η_pad) (b_band + η_pad)`, then any two visits `0 ≤ u₁ ≤ u₂ ≤ R` to `[a_band, b_band]`
satisfy `u₂ - u₁ ≤ ((b_band - a_band) / c_m) ^ (1 / m)`. -/
theorem holder_dini_collar_diam_le {m : ℕ} (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 R))
    {c_m a_band b_band η_pad : ℝ} (hc : 0 < c_m) (hab : a_band ≤ b_band) (hη_pad : 0 < η_pad)
    (hdini : ∀ s ∈ Icc (0 : ℝ) (R ^ m),
      g (s ^ ((m : ℝ)⁻¹)) ∈ Ioo (a_band - η_pad) (b_band + η_pad) →
      ∀ b ∈ Icc (0 : ℝ) (R ^ m), s < b → ∀ ε > 0,
        ∃ h ∈ Ioc (0 : ℝ) (b - s),
          (c_m - ε) * h ≤ g ((s + h) ^ ((m : ℝ)⁻¹)) - g (s ^ ((m : ℝ)⁻¹)))
    {u₁ u₂ : ℝ} (hu₁ : u₁ ∈ Icc 0 R) (hu₂ : u₂ ∈ Icc 0 R) (h12 : u₁ ≤ u₂)
    (hg₁ : g u₁ ∈ Icc a_band b_band) (hg₂ : g u₂ ∈ Icc a_band b_band) :
    u₂ - u₁ ≤ ((b_band - a_band) / c_m) ^ ((m : ℝ)⁻¹) := by
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hroot_pow {u : ℝ} (hu : 0 ≤ u) : (u ^ m) ^ ((m : ℝ)⁻¹) = u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu, mul_inv_cancel₀ hm_pos.ne', Real.rpow_one]
  have hmaps : MapsTo (fun s : ℝ => s ^ ((m : ℝ)⁻¹)) (Icc 0 (R ^ m)) (Icc 0 R) := by
    rintro s ⟨hs0, hsR⟩
    refine ⟨Real.rpow_nonneg hs0 _, ?_⟩
    calc s ^ ((m : ℝ)⁻¹) ≤ (R ^ m) ^ ((m : ℝ)⁻¹) :=
          Real.rpow_le_rpow hs0 hsR (inv_pos.mpr hm_pos).le
      _ = R := hroot_pow hR
  have hcont_reparam : ContinuousOn (fun s : ℝ => g (s ^ ((m : ℝ)⁻¹))) (Icc 0 (R ^ m)) :=
    hg.comp (continuousOn_id.rpow_const fun _ _ => Or.inr (inv_pos.mpr hm_pos).le) hmaps
  have hs₁ : u₁ ^ m ∈ Icc (0 : ℝ) (R ^ m) :=
    ⟨pow_nonneg hu₁.1 m, pow_le_pow_left₀ hu₁.1 hu₁.2 m⟩
  have hs₂ : u₂ ^ m ∈ Icc (0 : ℝ) (R ^ m) :=
    ⟨pow_nonneg hu₂.1 m, pow_le_pow_left₀ hu₂.1 hu₂.2 m⟩
  have hs12 : u₁ ^ m ≤ u₂ ^ m := pow_le_pow_left₀ hu₁.1 h12 m
  have hdiam_s := levelBand_dini_diam_le (convex_Icc 0 (R ^ m)) hcont_reparam hc hab hη_pad hdini
    hs₁ hs₂ hs12 (by rwa [hroot_pow hu₁.1]) (by rwa [hroot_pow hu₂.1])
  have hpow_diff : (u₂ - u₁) ^ m ≤ u₂ ^ m - u₁ ^ m := by
    have h := add_pow_ge_pow_add_pow (sub_nonneg.mpr h12) hu₁.1 hm
    rw [sub_add_cancel] at h
    linarith only [h]
  have hpow_le : (u₂ - u₁) ^ m ≤ (b_band - a_band) / c_m := hpow_diff.trans hdiam_s
  calc u₂ - u₁ = ((u₂ - u₁) ^ m) ^ ((m : ℝ)⁻¹) := (hroot_pow (sub_nonneg.mpr h12)).symm
    _ ≤ ((b_band - a_band) / c_m) ^ ((m : ℝ)⁻¹) :=
        Real.rpow_le_rpow (pow_nonneg (sub_nonneg.mpr h12) m) hpow_le (inv_pos.mpr hm_pos).le

/-- Product-Gaussian Hölder-Dini collar anti-concentration on `[0, R]` slices:
if for every `y : ι → ℝ`, `{t : ℝ | Function.update y i₀ t ∈ Ω} ⊆ Icc 0 R` and `±F` obeys `s = u^m`
right Dini coercivity `≥ c_m > 0` inside `Ioo (e₀ - η_pad) (e₀ + δ + η_pad)`, then
`ℙ(x ∈ Ω ∧ F x ∈ Ioc e₀ (e₀ + δ)) ≤ (δ / c_m) ^ (1 / m) / √(2 π)`. -/
theorem gaussian_holder_dini_collar_anticoncentration
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {F : (ι → ℝ) → ℝ} (hF : Measurable F)
    {Ω : Set (ι → ℝ)} (hΩ : MeasurableSet Ω)
    {m : ℕ} (hm : 1 ≤ m) {R c_m e₀ δ η_pad : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c_m) (hδ : 0 ≤ δ) (hη_pad : 0 < η_pad)
    (hfib : ∀ y : ι → ℝ, ∃ sgn : Bool,
      {t : ℝ | Function.update y i₀ t ∈ Ω} ⊆ Icc 0 R ∧
      ContinuousOn (fun t => F (Function.update y i₀ t)) (Icc 0 R) ∧
      ∀ s ∈ Icc (0 : ℝ) (R ^ m),
        F (Function.update y i₀ (s ^ ((m : ℝ)⁻¹))) ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad) →
        ∀ b ∈ Icc (0 : ℝ) (R ^ m), s < b → ∀ ε > 0,
          ∃ h ∈ Ioc (0 : ℝ) (b - s),
            (c_m - ε) * h ≤ (if sgn then 1 else -1) *
              (F (Function.update y i₀ ((s + h) ^ ((m : ℝ)⁻¹))) -
                F (Function.update y i₀ (s ^ ((m : ℝ)⁻¹))))) :
    (Measure.pi fun _ : ι => gaussianReal 0 1).real
      {x ∈ Ω | F x ∈ Ioc e₀ (e₀ + δ)} ≤
      (δ / c_m) ^ ((m : ℝ)⁻¹) / Real.sqrt (2 * Real.pi) := by
  let w_max := (δ / c_m) ^ ((m : ℝ)⁻¹)
  have hw_nn : 0 ≤ w_max := Real.rpow_nonneg (div_nonneg hδ hc.le) _
  have hB_nn : 0 ≤ w_max / Real.sqrt (2 * Real.pi) := div_nonneg hw_nn (by positivity)
  refine gaussian_pi_le_of_fiber_bound i₀ (hΩ.inter (hF measurableSet_Ioc)) hB_nn fun y => ?_
  obtain ⟨sgn, hsub_R, hcont, hdini⟩ := hfib y
  let g : ℝ → ℝ := fun t => F (Function.update y i₀ t)
  let A := {t : ℝ | Function.update y i₀ t ∈ Ω ∧ g t ∈ Ioc e₀ (e₀ + δ)}
  have hbox : ∃ a₀ : ℝ, A ⊆ Icc a₀ (a₀ + w_max) := by
    by_cases hA : A = ∅
    · exact ⟨0, by rw [hA]; exact empty_subset _⟩
    · obtain ⟨t₀, ht₀⟩ := nonempty_iff_ne_empty.mpr hA
      have hdiam : ∀ t₁ ∈ A, ∀ t₂ ∈ A, t₁ ≤ t₂ → t₂ - t₁ ≤ w_max := by
        intro t₁ ht₁ t₂ ht₂ h12
        by_cases hsgn : sgn = true
        · have hd_pos : ∀ s ∈ Icc (0 : ℝ) (R ^ m),
              g (s ^ ((m : ℝ)⁻¹)) ∈ Ioo (e₀ - η_pad) ((e₀ + δ) + η_pad) →
              ∀ b ∈ Icc (0 : ℝ) (R ^ m), s < b → ∀ ε > 0,
                ∃ h ∈ Ioc (0 : ℝ) (b - s),
                  (c_m - ε) * h ≤ g ((s + h) ^ ((m : ℝ)⁻¹)) - g (s ^ ((m : ℝ)⁻¹)) := by
            intro s hs hgs b hb hsb ε hε
            obtain ⟨h, hh_mem, hh_le⟩ := hdini s hs hgs b hb hsb ε hε
            rw [if_pos hsgn, one_mul] at hh_le
            exact ⟨h, hh_mem, hh_le⟩
          have hb := holder_dini_collar_diam_le hm hR hcont hc (by linarith only [hδ]) hη_pad
            hd_pos (hsub_R ht₁.1) (hsub_R ht₂.1) h12 ⟨ht₁.2.1.le, ht₁.2.2⟩ ⟨ht₂.2.1.le, ht₂.2.2⟩
          simpa only [w_max, add_sub_cancel_left] using hb
        · let g_neg : ℝ → ℝ := fun t => -g t
          have hd_neg : ∀ s ∈ Icc (0 : ℝ) (R ^ m),
              g_neg (s ^ ((m : ℝ)⁻¹)) ∈ Ioo (-(e₀ + δ) - η_pad) (-e₀ + η_pad) →
              ∀ b ∈ Icc (0 : ℝ) (R ^ m), s < b → ∀ ε > 0,
                ∃ h ∈ Ioc (0 : ℝ) (b - s),
                  (c_m - ε) * h ≤ g_neg ((s + h) ^ ((m : ℝ)⁻¹)) - g_neg (s ^ ((m : ℝ)⁻¹)) := by
            intro s hs hgs b hb hsb ε hε
            have hgs' : g (s ^ ((m : ℝ)⁻¹)) ∈ Ioo (e₀ - η_pad) (e₀ + δ + η_pad) :=
              ⟨by dsimp [g_neg] at hgs; linarith only [hgs.2],
               by dsimp [g_neg] at hgs; linarith only [hgs.1]⟩
            obtain ⟨h, hh_mem, hh_le⟩ := hdini s hs hgs' b hb hsb ε hε
            rw [if_neg hsgn] at hh_le
            exact ⟨h, hh_mem, by dsimp [g_neg]; linarith only [hh_le]⟩
          have hb := holder_dini_collar_diam_le hm hR hcont.neg hc (by linarith only [hδ]) hη_pad
            hd_neg (hsub_R ht₁.1) (hsub_R ht₂.1) h12
            ⟨by dsimp [g_neg]; linarith only [ht₁.2.2], by dsimp [g_neg]; linarith only [ht₁.2.1]⟩
            ⟨by dsimp [g_neg]; linarith only [ht₂.2.2], by dsimp [g_neg]; linarith only [ht₂.2.1]⟩
          have hlen : -e₀ - -(e₀ + δ) = δ := by ring
          simpa only [w_max, hlen] using hb
      have hbdd : BddBelow A := ⟨0, fun t ht => (hsub_R ht.1).1⟩
      let a₀ := sInf A
      refine ⟨a₀, fun t ht => ⟨csInf_le hbdd ht, ?_⟩⟩
      have hlb : t - w_max ≤ a₀ := le_csInf ⟨t₀, ht₀⟩ fun u hu => by
        rcases le_total u t with hut | htu
        · linarith only [hdiam u hu t ht hut]
        · linarith only [htu, hw_nn]
      linarith only [hlb]
  obtain ⟨a₀, ha₀⟩ := hbox
  calc (gaussianReal 0 1) A
      ≤ (gaussianReal 0 1) (Icc a₀ (a₀ + w_max)) := measure_mono ha₀
    _ ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹) * volume (Icc a₀ (a₀ + w_max)) :=
        gaussianReal_le_inv_sqrt_two_pi_vol_hd _
    _ = ENNReal.ofReal (w_max / Real.sqrt (2 * Real.pi)) := by
        rw [Real.volume_Icc, add_sub_cancel_left, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-! ## Section 3: `U(2)^⊗N` left-invariance obstruction of `1`-local spin-flip lines vs.
Euler-shuffle identity and `2`-local second-order Dyson escape -/

private def kronTwoQubitPair (R₁ R₂ : Matrix Bool Bool ℂ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun p q => R₁ p.1 q.1 * R₂ p.2 q.2

private theorem kronTwoQubitPair_mem_unitary {R₁ R₂ : Matrix Bool Bool ℂ}
    (hR₁ : star R₁ * R₁ = 1 ∧ R₁ * star R₁ = 1)
    (hR₂ : star R₂ * R₂ = 1 ∧ R₂ * star R₂ = 1) :
    kronTwoQubitPair R₁ R₂ ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Unitary.mem_iff]
  have hst : star (kronTwoQubitPair R₁ R₂) =
      fun p q => (star R₁) p.1 q.1 * (star R₂) p.2 q.2 := by
    ext p q; simp [kronTwoQubitPair, star_mul']
  rw [hst]
  constructor <;> ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ <;> simp only [kronTwoQubitPair, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, Prod.ext_iff]
  · have hf : (∑ x : Bool, ∑ y : Bool,
        ((star R₁) p₁ x * (star R₂) p₂ y) * (R₁ x q₁ * R₂ y q₂)) =
        ((star R₁ * R₁) p₁ q₁) * ((star R₂ * R₂) p₂ q₂) := by
      simp only [Matrix.mul_apply]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hf, hR₁.1, hR₂.1, Matrix.one_apply, Matrix.one_apply]
    by_cases hp1 : p₁ = q₁ <;> by_cases hp2 : p₂ = q₂ <;> simp [hp1, hp2]
  · have hf : (∑ x : Bool, ∑ y : Bool,
        (R₁ p₁ x * R₂ p₂ y) * ((star R₁) x q₁ * (star R₂) y q₂)) =
        ((R₁ * star R₁) p₁ q₁) * ((R₂ * star R₂) p₂ q₂) := by
      simp only [Matrix.mul_apply]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hf, hR₁.2, hR₂.2, Matrix.one_apply, Matrix.one_apply]
    by_cases hp1 : p₁ = q₁ <;> by_cases hp2 : p₂ = q₂ <;> simp [hp1, hp2]

private theorem prodLocal_hetero_conj_twoQubitLiftMatrix {N : ℕ}
    (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (a b : Fin N) (hab : a ≠ b) (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    prodLocalMatrix R * twoQubitLiftMatrix a b hab U * star (prodLocalMatrix R) =
      twoQubitLiftMatrix a b hab
        (kronTwoQubitPair (R a) (R b) * U * star (kronTwoQubitPair (R a) (R b))) := by
  let W := prodLocalMatrix R
  have hlift_apply (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (u v : Config N) :
      twoQubitLiftMatrix a b hab M u v =
        if ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s then M (u a, u b) (v a, v b) else 0 := by
    dsimp only [twoQubitLiftMatrix, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [Equiv.symm_symm]
    change (Matrix.kroneckerMap (· * ·) M 1)
      (splitTwoQubitConfig a b hab u) (splitTwoQubitConfig a b hab v) = _
    rw [Matrix.kroneckerMap_apply]
    by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
    · rw [if_pos hall]
      have hrest : (splitTwoQubitConfig a b hab u).2 = (splitTwoQubitConfig a b hab v).2 := by
        ext ⟨s, hs⟩; exact hall s hs.1 hs.2
      rw [hrest, Matrix.one_apply_eq, mul_one]; rfl
    · rw [if_neg hall]
      have hrest_ne : (splitTwoQubitConfig a b hab u).2 ≠ (splitTwoQubitConfig a b hab v).2 := by
        intro heq; apply hall; intro s hsa hsb
        exact congrFun heq ⟨s, hsa, hsb⟩
      rw [Matrix.one_apply_ne hrest_ne, mul_zero]
  let pairSet : Finset (Fin N) := {a, b}
  have hfactor (A B : Matrix Bool Bool ℂ) :
      twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) =
        prodLocalMatrix (fun s => if s = a then A else if s = b then B else 1) := by
    ext u v
    rw [hlift_apply]
    dsimp only [prodLocalMatrix]
    rw [← Finset.prod_mul_prod_compl pairSet, Finset.prod_pair hab]
    simp only [↓reduceIte, hab.symm]
    have hrest : (∏ s ∈ pairSetᶜ,
        (if s = a then A else if s = b then B else 1) (u s) (v s)) =
        if ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s then 1 else 0 := by
      have h1 : ∀ s ∈ pairSetᶜ,
          (if s = a then A else if s = b then B else 1) (u s) (v s) =
            if u s = v s then 1 else 0 := by
        intro s hs
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        simp [hs.1, hs.2, Matrix.one_apply]
      rw [Finset.prod_congr rfl h1]
      by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
      · rw [if_pos hall]
        refine Finset.prod_eq_one fun s hs => ?_
        simp only [pairSet, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        rw [if_pos (hall s hs.1 hs.2)]
      · rw [if_neg hall]; push Not at hall
        obtain ⟨s, hsa, hsb, hne⟩ := hall
        exact Finset.prod_eq_zero (by simp [pairSet, hsa, hsb]) (if_neg hne)
    rw [hrest]
    split_ifs <;> ring
  have hconj_factor (A B : Matrix Bool Bool ℂ) :
      W * twoQubitLiftMatrix a b hab (fun p q => A p.1 q.1 * B p.2 q.2) * star W =
        twoQubitLiftMatrix a b hab
          (fun p q => (R a * A * star (R a)) p.1 q.1 * (R b * B * star (R b)) p.2 q.2) := by
    rw [hfactor A B, hfactor (R a * A * star (R a)) (R b * B * star (R b))]
    dsimp only [W]
    rw [prodLocalMatrix_star, prodLocalMatrix_mul, prodLocalMatrix_mul]
    congr 1; funext s
    by_cases hsa : s = a
    · simp [hsa]
    · by_cases hsb : s = b
      · simp [hsa, hsb]
      · simp [hsa, hsb, mul_one, (hR s).2]
  let E₁ (p q : Bool) : Matrix Bool Bool ℂ := fun x y => if x = p ∧ y = q then 1 else 0
  have hU_sum : twoQubitLiftMatrix a b hab U =
      ∑ p : Bool × Bool, ∑ q : Bool × Bool,
        U p q • twoQubitLiftMatrix a b hab (fun r s => E₁ p.1 q.1 r.1 s.1 * E₁ p.2 q.2 r.2 s.2) := by
    ext u v
    rw [hlift_apply, Matrix.sum_apply]
    simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
    by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
    · simp only [if_pos hall]
      rw [Finset.sum_eq_single (u a, u b)]
      · rw [Finset.sum_eq_single (v a, v b)]
        · simp [E₁]
        · intro q _ hq
          have h0 : E₁ (u a) q.1 (u a) (v a) * E₁ (u b) q.2 (u b) (v b) = 0 := by
            by_cases h1 : v a = q.1
            · have h2 : v b ≠ q.2 := fun h => hq (Prod.ext h1.symm h.symm)
              simp [E₁, h2]
            · simp [E₁, h1]
          rw [h0, mul_zero]
        · simp
      · intro p _ hp
        refine Finset.sum_eq_zero fun q _ => ?_
        have h0 : E₁ p.1 q.1 (u a) (v a) * E₁ p.2 q.2 (u b) (v b) = 0 := by
          by_cases h1 : u a = p.1
          · have h2 : u b ≠ p.2 := fun h => hp (Prod.ext h1.symm h.symm)
            simp [E₁, h2]
          · simp [E₁, h1]
        rw [h0, mul_zero]
      · simp
    · simp [if_neg hall]
  change W * twoQubitLiftMatrix a b hab U * star W = _
  rw [hU_sum, Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hconj_factor]
  ext u v
  rw [hlift_apply, Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, Matrix.smul_apply, hlift_apply, smul_eq_mul]
  by_cases hall : ∀ s : Fin N, s ≠ a → s ≠ b → u s = v s
  · simp only [if_pos hall]
    have hE1 (R₀ : Matrix Bool Bool ℂ) (p₀ q₀ x₀ z₀ : Bool) :
        (R₀ * E₁ p₀ q₀ * star R₀) x₀ z₀ = R₀ x₀ p₀ * (star R₀) q₀ z₀ := by
      simp only [Matrix.mul_apply, Fintype.sum_bool, E₁]
      cases p₀ <;> cases q₀ <;> simp
    have hstR₂ (q : Bool × Bool) :
        (star (kronTwoQubitPair (R a) (R b))) q (v a, v b) =
          (star (R a)) q.1 (v a) * (star (R b)) q.2 (v b) := by
      simp [kronTwoQubitPair, star_mul']
    have hrhs : (kronTwoQubitPair (R a) (R b) * U * star (kronTwoQubitPair (R a) (R b)))
        (u a, u b) (v a, v b) =
        ∑ p : Bool × Bool, ∑ q : Bool × Bool,
          U p q * (kronTwoQubitPair (R a) (R b) (u a, u b) p *
            (star (kronTwoQubitPair (R a) (R b))) q (v a, v b)) := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hrhs]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hE1, hE1, hstR₂ q]
    dsimp only [kronTwoQubitPair]
    ring
  · simp [if_neg hall]

private theorem realizes_one_twoQubitLiftMatrix_hd {N : ℕ} (a b : Fin N) (hab : a ≠ b)
    (V : Matrix.unitaryGroup (Bool × Bool) ℂ) :
    Realizes 1 (twoQubitLiftMatrix a b hab V.val) := by
  let z_loc := scalarSpecialUnitaryPhase V
  let G_loc := scalarSpecialUnitaryRepresentative V
  have hz_unit : star z_loc * z_loc = 1 := scalarSpecialUnitaryPhase_unitary V
  have hznorm : ‖star z_loc‖ = 1 := by
    have hnorm := congrArg norm hz_unit
    have hsq : ‖z_loc‖ * ‖z_loc‖ = 1 := by simpa [norm_mul] using hnorm
    have hz0 : ‖z_loc‖ = 1 := by nlinarith [norm_nonneg z_loc, sq_nonneg (‖z_loc‖ - 1)]
    simpa using hz0
  refine ⟨star z_loc, hznorm, TwoQubitCircuit.singleOn a b hab G_loc, le_rfl, ?_⟩
  rw [TwoQubitCircuit.singleOn_eval]
  have hgate : (twoQubitLift a b hab G_loc : Register N) =
      z_loc • twoQubitLiftMatrix a b hab V.val := by
    ext x y
    simp [G_loc, z_loc, twoQubitLift, twoQubitLiftMatrix,
      specialUnitaryAsUnitary, scalarSpecialUnitaryRepresentative_coe,
      unitaryGroupReindex_coe, Quantum.tensorGate_val,
      Matrix.reindex_apply, Matrix.kronecker, Matrix.smul_apply]
    ring
  rw [hgate, smul_smul, hz_unit, one_smul]

private theorem conj_mem_phaseCircuitMatrixImageAtMost_prodLocal {N j : ℕ}
    (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    {W₀ : Register N} (hW₀ : W₀ ∈ phaseCircuitMatrixImageAtMost N j) :
    prodLocalMatrix R * W₀ * star (prodLocalMatrix R) ∈ phaseCircuitMatrixImageAtMost N j := by
  obtain ⟨z, hz, C, hC, rfl⟩ := mem_phaseCircuitMatrixImageAtMost_iff.mp hW₀
  have hW_unit := prodLocalMatrix_mem_unitary R hR
  obtain ⟨hWL, hWR⟩ := Unitary.mem_iff.mp hW_unit
  have hlist : ∀ L : List (UGroup N),
      (∀ g ∈ L, Realizes 1 (prodLocalMatrix R * g.val * star (prodLocalMatrix R))) →
      Realizes L.length (prodLocalMatrix R * L.prod.val * star (prodLocalMatrix R)) := by
    intro L hL
    induction L with
    | nil =>
        rw [List.length_nil, List.prod_nil, OneMemClass.coe_one, mul_one, hWR]
        exact DiagonalSynthesis.Realizes.one N
    | cons g rest ih =>
        have hsplit : prodLocalMatrix R * (g.val * rest.prod.val) * star (prodLocalMatrix R) =
            (prodLocalMatrix R * g.val * star (prodLocalMatrix R)) *
              (prodLocalMatrix R * rest.prod.val * star (prodLocalMatrix R)) := by
          calc prodLocalMatrix R * (g.val * rest.prod.val) * star (prodLocalMatrix R)
              = prodLocalMatrix R * g.val * (star (prodLocalMatrix R) * prodLocalMatrix R) *
                  rest.prod.val * star (prodLocalMatrix R) := by
                    rw [hWL, mul_one]; simp only [mul_assoc]
            _ = _ := by simp only [mul_assoc]
        rw [List.length_cons, Nat.add_comm, List.prod_cons, Submonoid.coe_mul, hsplit]
        exact DiagonalSynthesis.Realizes.mul
          (hL g (List.mem_cons.mpr (Or.inl rfl)))
          (ih fun x hx => hL x (List.mem_cons.mpr (Or.inr hx)))
  let L_gates : List (UGroup N) :=
    (List.ofFn fun r => C.architecture.gateLift r (C.gates r)).reverse
  have hlen : L_gates.length = C.gateCount := by simp [L_gates]
  have hprod_eq : L_gates.prod = C.eval := rfl
  have hmem : ∀ g ∈ L_gates,
      Realizes 1 (prodLocalMatrix R * g.val * star (prodLocalMatrix R)) := by
    intro g hg
    rw [List.mem_reverse] at hg
    refine ((List.forall_mem_ofFn_iff
      (P := fun g : UGroup N =>
        Realizes 1 (prodLocalMatrix R * g.val * star (prodLocalMatrix R)))).mpr fun r => ?_) g hg
    let a := (C.architecture.sites r).1
    let b := (C.architecture.sites r).2
    let hab := C.architecture.distinct r
    let G0 := C.gates r
    have hR_pair : kronTwoQubitPair (R a) (R b) ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
      kronTwoQubitPair_mem_unitary (hR a) (hR b)
    have hlift_val : (C.architecture.gateLift r G0).val =
        twoQubitLiftMatrix a b hab (specialUnitaryAsUnitary G0).val := by
      ext x y
      simp only [TwoQubitArchitecture.gateLift, twoQubitLift, twoQubitLiftMatrix,
        unitaryGroupReindex_coe, Quantum.tensorGate_val, OneMemClass.coe_one,
        Matrix.kronecker, Matrix.reindex_apply, Matrix.submatrix_apply, a, b, G0]
    rw [hlift_val, prodLocal_hetero_conj_twoQubitLiftMatrix R hR a b hab]
    exact realizes_one_twoQubitLiftMatrix_hd a b hab
      ⟨kronTwoQubitPair (R a) (R b) * (specialUnitaryAsUnitary G0).val *
        star (kronTwoQubitPair (R a) (R b)),
        mul_mem (mul_mem hR_pair (specialUnitaryAsUnitary G0).2) (Unitary.star_mem hR_pair)⟩
  have hcirc : Realizes C.gateCount
      (prodLocalMatrix R * C.eval.val * star (prodLocalMatrix R)) := by
    rw [← hlen, ← hprod_eq]
    exact hlist L_gates hmem
  obtain ⟨z', hz', C', hC', heq'⟩ := hcirc
  refine mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨z * z', by rw [norm_mul, hz, hz', mul_one],
    C', hC'.trans hC, ?_⟩
  rw [Matrix.mul_smul, Matrix.smul_mul, heq', smul_smul]

/-- Exact left `U(2)^⊗N`-gauge invariance of `torusCriticalHeight`: multiplying an eigenframe
`V : UGroup N` on the left by any heterogeneous local unitary `prodLocalMatrix R` (`R_s ∈ U(2)`)
leaves `torusCriticalHeight e · j` identically unchanged. -/
theorem torusCriticalHeight_prodLocal_left_eq {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (R : Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ s, star (R s) * R s = 1 ∧ R s * star (R s) = 1)
    (V : UGroup N) (j : ℕ) :
    torusCriticalHeight e ⟨prodLocalMatrix R * V.val, mul_mem (prodLocalMatrix_mem_unitary R hR) V.2⟩ j =
      torusCriticalHeight e V j := by
  let W_loc := prodLocalMatrix R
  have hW_unit : W_loc ∈ unitary (Register N) := prodLocalMatrix_mem_unitary R hR
  obtain ⟨hWL, hWR⟩ := Unitary.mem_iff.mp hW_unit
  have hR_st : ∀ s, star (star (R s)) * star (R s) = 1 ∧ star (R s) * star (star (R s)) = 1 :=
    fun s => by rw [star_star]; exact ⟨(hR s).2, (hR s).1⟩
  have hpt_eq (θ : Fin d → UnitAddCircle) :
      Metric.infDist
        (projectiveSpectralMatrix e ⟨W_loc * V.val, mul_mem hW_unit V.2⟩ θ)
        (phaseCircuitMatrixImageAtMost N j) =
      Metric.infDist (projectiveSpectralMatrix e V θ) (phaseCircuitMatrixImageAtMost N j) := by
    have hspec : projectiveSpectralMatrix e ⟨W_loc * V.val, mul_mem hW_unit V.2⟩ θ =
        W_loc * projectiveSpectralMatrix e V θ * star W_loc := by
      unfold projectiveSpectralMatrix
      have hinv1 : (⟨W_loc * V.val, mul_mem hW_unit V.2⟩⁻¹ : UGroup N).val =
          star V.val * star W_loc := star_mul W_loc V.val
      have hinv2 : (V⁻¹ : UGroup N).val = star V.val := rfl
      rw [hinv1, hinv2]; simp only [mul_assoc]
    rw [hspec]
    have hC_ne : (phaseCircuitMatrixImageAtMost N j).Nonempty :=
      ⟨(1 : ℂ) • ((TwoQubitCircuit.one N).eval : Register N),
        mem_phaseCircuitMatrixImageAtMost_iff.mpr ⟨1, norm_one, TwoQubitCircuit.one N, Nat.zero_le _, rfl⟩⟩
    apply le_antisymm
    · refine (Metric.infDist_le_iff hC_ne).2 fun ε hε => ?_
      obtain ⟨M, hM_mem, hM_lt⟩ := (Metric.infDist_lt_iff hC_ne).1
        (lt_add_of_pos_right _ hε)
      refine ⟨W_loc * M * star W_loc, conj_mem_phaseCircuitMatrixImageAtMost_prodLocal R hR hM_mem, ?_⟩
      rw [dist_eq_norm, ← Matrix.sub_mul, ← Matrix.mul_sub, l2_opNorm_unitary_conj_eq hW_unit,
        ← dist_eq_norm]
      exact hM_lt
    · refine (Metric.infDist_le_iff hC_ne).2 fun ε hε => ?_
      obtain ⟨M, hM_mem, hM_lt⟩ := (Metric.infDist_lt_iff hC_ne).1
        (lt_add_of_pos_right _ hε)
      let M' := prodLocalMatrix (fun s => star (R s)) * M *
        star (prodLocalMatrix (fun s => star (R s)))
      have hM'_mem : M' ∈ phaseCircuitMatrixImageAtMost N j :=
        conj_mem_phaseCircuitMatrixImageAtMost_prodLocal (fun s => star (R s)) hR_st hM_mem
      have hconj_M' : W_loc * M' * star W_loc = M := by
        dsimp [M', W_loc]
        rw [← prodLocalMatrix_star R, star_star]
        calc prodLocalMatrix R * (star (prodLocalMatrix R) * M * prodLocalMatrix R) *
              star (prodLocalMatrix R)
            = (W_loc * star W_loc) * M * (W_loc * star W_loc) := by simp only [W_loc, mul_assoc]
          _ = M := by rw [hWR, one_mul, mul_one]
      refine ⟨M', hM'_mem, ?_⟩
      rw [dist_eq_norm, ← l2_opNorm_unitary_conj_eq hW_unit, Matrix.mul_sub, Matrix.sub_mul,
        hconj_M', ← dist_eq_norm]
      exact hM_lt
  unfold torusCriticalHeight
  congr 1; ext y
  simp only [mem_range, hpt_eq]

/-- Every `1`-local spin-flip eigenframe curve `u ↦ prodLocalMatrix (R u) * V₀` has **identically
constant** `torusCriticalHeight` and hence zero `k`-th iterated derivative for all `k ≥ 1`. -/
theorem torusCriticalHeight_const_along_localUnitary_curve {N d : ℕ} (e : Config N ≃ Fin (d + 1))
    (R : ℝ → Fin N → Matrix Bool Bool ℂ)
    (hR : ∀ u s, star (R u s) * R u s = 1 ∧ R u s * star (R u s) = 1)
    (V₀ : UGroup N) (j : ℕ) :
    (∀ u : ℝ,
      torusCriticalHeight e
        ⟨prodLocalMatrix (R u) * V₀.val, mul_mem (prodLocalMatrix_mem_unitary (R u) (hR u)) V₀.2⟩ j =
        torusCriticalHeight e V₀ j) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ u₀ : ℝ,
      iteratedDeriv k
        (fun u : ℝ => torusCriticalHeight e
          ⟨prodLocalMatrix (R u) * V₀.val, mul_mem (prodLocalMatrix_mem_unitary (R u) (hR u)) V₀.2⟩ j)
        u₀ = 0) := by
  have hconst : ∀ u : ℝ,
      torusCriticalHeight e
        ⟨prodLocalMatrix (R u) * V₀.val, mul_mem (prodLocalMatrix_mem_unitary (R u) (hR u)) V₀.2⟩ j =
        torusCriticalHeight e V₀ j :=
    fun u => torusCriticalHeight_prodLocal_left_eq e (R u) (hR u) V₀ j
  refine ⟨hconst, fun k hk u₀ => ?_⟩
  rw [show (fun u : ℝ => torusCriticalHeight e
      ⟨prodLocalMatrix (R u) * V₀.val, mul_mem (prodLocalMatrix_mem_unitary (R u) (hR u)) V₀.2⟩ j) =
      fun _ : ℝ => torusCriticalHeight e V₀ j from funext hconst]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk) with ⟨k', rfl⟩
  rw [iteratedDeriv_succ']
  simp [deriv_const]

/-- Exact `m!`-term Euler-shuffle geodesic reciprocal identity: for any `B : Fin m → ℝ` with
`∀ j, 0 < B j`, summing the ordered Dyson energy-denominator products over all `m!` spin-flip
orderings `π ∈ S_m` collapses identically to `∏_{j : Fin m} (B j)⁻¹`. -/
theorem euler_shuffle_reciprocal_sum :
    ∀ {m : ℕ} (B : Fin m → ℝ), (∀ j : Fin m, 0 < B j) →
      (∑ π : Equiv.Perm (Fin m),
        ∏ r : Fin m, (∑ j : Fin m, if r ≤ j then B (π j) else 0)⁻¹) =
        ∏ j : Fin m, (B j)⁻¹
  | 0, B, _ => by simp
  | m + 1, B, hB => by
      let S_tot : ℝ := ∑ j : Fin (m + 1), B j
      have hS_pos : 0 < S_tot :=
        Finset.sum_pos (fun j _ => hB j) ⟨0, Finset.mem_univ 0⟩
      let B_sub (p : Fin (m + 1)) : Fin m → ℝ := fun k => B (Equiv.swap 0 p k.succ)
      have hB_sub_pos (p : Fin (m + 1)) (k : Fin m) : 0 < B_sub p k := hB _
      rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
      have hterm_pe (p : Fin (m + 1)) (e : Equiv.Perm (Fin m)) :
          (∏ r : Fin (m + 1),
            (∑ j : Fin (m + 1), if r ≤ j then B (Equiv.Perm.decomposeFin.symm (p, e) j) else 0)⁻¹) =
            S_tot⁻¹ * ∏ r' : Fin m,
              (∑ j' : Fin m, if r' ≤ j' then B_sub p (e j') else 0)⁻¹ := by
        rw [Fin.prod_univ_succ]
        congr 1
        · have h0 : (∑ j : Fin (m + 1),
              if (0 : Fin (m + 1)) ≤ j then B (Equiv.Perm.decomposeFin.symm (p, e) j) else 0) =
              S_tot := by
            simp only [Fin.zero_le, ↓reduceIte]
            exact Equiv.Perm.sum_comp _ Finset.univ _ (by simp)
          rw [h0]
        · refine Finset.prod_congr rfl fun r' _ => ?_
          congr 1
          rw [Fin.sum_univ_succ]
          have hn0 : ¬ (r'.succ ≤ (0 : Fin (m + 1))) := not_le_of_gt (Fin.succ_pos r')
          rw [if_neg hn0, zero_add]
          refine Finset.sum_congr rfl fun j' _ => ?_
          simp only [Fin.succ_le_succ_iff, Equiv.Perm.decomposeFin_symm_apply_succ, B_sub]
      simp_rw [hterm_pe, ← Finset.mul_sum]
      have hsub_prod (p : Fin (m + 1)) :
          (∏ k : Fin m, (B_sub p k)⁻¹) = B p * ∏ j : Fin (m + 1), (B j)⁻¹ := by
        have hperm : (∏ j : Fin (m + 1), (B j)⁻¹) =
            ∏ j : Fin (m + 1), (B (Equiv.swap 0 p j))⁻¹ :=
          ((Equiv.swap (0 : Fin (m + 1)) p).prod_comp fun j => (B j)⁻¹).symm
        rw [hperm, Fin.prod_univ_succ, Equiv.swap_apply_left]
        dsimp only [B_sub]
        have hBp_ne : B p ≠ 0 := (hB p).ne'
        field_simp [hBp_ne]
      have hinner (p : Fin (m + 1)) :
          (∑ e : Equiv.Perm (Fin m),
            ∏ r' : Fin m, (∑ j' : Fin m, if r' ≤ j' then B_sub p (e j') else 0)⁻¹) =
            B p * ∏ j : Fin (m + 1), (B j)⁻¹ :=
        (euler_shuffle_reciprocal_sum (B_sub p) (hB_sub_pos p)).trans (hsub_prod p)
      simp_rw [hinner]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      change (∑ p : Fin (m + 1), S_tot⁻¹ * B p) * ∏ j : Fin (m + 1), (B j)⁻¹ = _
      rw [← Finset.mul_sum]
      change (S_tot⁻¹ * S_tot) * ∏ j : Fin (m + 1), (B j)⁻¹ = _
      rw [inv_mul_cancel₀ hS_pos.ne', one_mul]

/-- Second-order Rayleigh–Schrödinger / Dyson off-diagonal eigenstate amplitude
`((E b - E a)⁻¹) * ∑_{c : E c ≠ E b} P_{a c} P_{c b} / (E b - E c)` between basis states `a, b`. -/
def secondOrderDysonOffDiag {N : ℕ} (E : Config N → ℝ) (P : Register N) (a b : Config N) : ℂ :=
  (((E b - E a : ℝ) : ℂ)⁻¹) *
    ∑ c ∈ Finset.univ.filter (fun c : Config N => E c ≠ E b),
      (P a c * P c b) / ((E b - E c : ℝ) : ℂ)

/-- Explicit `2`-local second-order Dyson escape from the Hamming-distance-`3` first-order Kato
blind spot (`N = n + 2 ≥ 3`): for `E_diag(x) = ∑_s (±1) 2^s`, `x₀ = 0^N`, `x₁ = 1^3 0^{N-3}`, and
the `2`-local chain perturbation `V_chain = X_0 X_1 + X_2 = pathHamiltonian u_ent` (`u_ent ∈ PathShell n`):
1. Every chain shell `u : PathShell n` (including `u_ent`) has zero first-order off-diagonal Kato
   entry `(basisKatoGenerator 1 E_diag ⟨H(u), _⟩)_{x₀, x₁} = 0` (`Hamming(x₀, x₁) = 3`),
2. `V_chain` has strictly nonzero second-order Dyson off-diagonal amplitude
   `secondOrderDysonOffDiag E_diag V_chain x₀ x₁ = 1 / 48 ≠ 0` (`1 / (14 * 8) + 1 / (14 * 6) = 1 / 48`),
3. `unitaryEvolution V_chain (π / 4)` is **not** in `Set.range prodLocalMatrix` (breaking `U(2)^⊗N`
   local separability via a nonzero `2 × 2` Bell minor `-i / 4 ≠ 0` on qubits `(0, 1)`). -/
theorem twoLocal_secondOrder_dyson_escapes_hammingThree_blindSpot {n : ℕ} (hn : 1 ≤ n) :
    let N := n + 2
    let E_diag : Config N → ℝ :=
      fun x => ∑ s : Fin N, (if x s then (1 : ℝ) else -1) * (2 : ℝ) ^ s.val
    let x₀ : Config N := fun _ => false
    let x₁ : Config N := fun s => decide (s.val < 3)
    let s₂ : Fin N := ⟨2, by omega⟩
    let u_ent : PathShell n :=
      WithLp.toLp 2 fun l : PathLabel n =>
        if l = .inr (0, (0, 0)) ∨ l = .inl (s₂, 0) then 1 else 0
    let V_chain : Register N := pathHamiltonian u_ent
    (∀ u : PathShell n,
      (basisKatoGenerator (1 : UGroup N) E_diag
        ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩).val x₀ x₁ = 0) ∧
    secondOrderDysonOffDiag E_diag V_chain x₀ x₁ = (1 / 48 : ℂ) ∧
    unitaryEvolution V_chain (Real.pi / 4) ∉ Set.range (@prodLocalMatrix N) := by
  intro N E_diag x₀ x₁ s₂ u_ent V_chain
  let s₀ : Fin N := ⟨0, by omega⟩
  let s₁ : Fin N := ⟨1, by omega⟩
  have hs01 : s₀ ≠ s₁ := fun h => by have hv : (0 : ℕ) = 1 := congrArg Fin.val h; omega
  have hs02 : s₀ ≠ s₂ := fun h => by have hv : (0 : ℕ) = 2 := congrArg Fin.val h; omega
  have hs12 : s₁ ≠ s₂ := fun h => by have hv : (1 : ℕ) = 2 := congrArg Fin.val h; omega
  -- Part 1: Every `PathShell n` vanishes on `(x₀, x₁)` at first Kato order.
  have hkato_zero : ∀ u : PathShell n,
      (basisKatoGenerator (1 : UGroup N) E_diag
        ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩).val x₀ x₁ = 0 := by
    intro u
    have hpauli0 (l : PathLabel n) : finitePauliMatrix (pathWord l) x₀ x₁ = 0 := by
      obtain ⟨t, ht3, ht_none⟩ : ∃ t : Fin N, t.val < 3 ∧ pathWord l t = none := by
        rcases l with ⟨s, q⟩ | ⟨e, pq⟩
        · by_cases hs : s.val = 0
          · refine ⟨s₁, by decide, ?_⟩
            have hne : s₁ ≠ s := fun h => by have hv : 1 = s.val := congrArg Fin.val h; omega
            simp [pathWord, onsiteWord, hne]
          · refine ⟨s₀, by decide, ?_⟩
            have hne : s₀ ≠ s := fun h => by have hv : 0 = s.val := congrArg Fin.val h; omega
            simp [pathWord, onsiteWord, hne]
        · by_cases he : e.val = 0
          · refine ⟨s₂, by decide, ?_⟩
            have h1 : s₂ ≠ e.castSucc := fun h => by have hv : 2 = e.val := congrArg Fin.val h; omega
            have h2 : s₂ ≠ e.succ := fun h => by have hv : 2 = e.val + 1 := congrArg Fin.val h; omega
            simp [pathWord, couplingWord, h1, h2]
          · refine ⟨s₀, by decide, ?_⟩
            have h1 : s₀ ≠ e.castSucc := fun h => by have hv : 0 = e.val := congrArg Fin.val h; omega
            have h2 : s₀ ≠ e.succ := fun h => by have hv : 0 = e.val + 1 := congrArg Fin.val h; omega
            simp [pathWord, couplingWord, h1, h2]
      unfold finitePauliMatrix
      refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
      rw [ht_none]
      have hdiff : x₀ t ≠ x₁ t := by simp [x₀, x₁, ht3]
      simp [boolPauliOptionEntry, boolPauliOption, hdiff]
    have hHu0 : pathHamiltonian u x₀ x₁ = 0 := by
      rw [pathHamiltonian_eq_sum, Matrix.sum_apply]
      exact Finset.sum_eq_zero fun l _ => by rw [Matrix.smul_apply, hpauli0 l, smul_zero]
    have h1val : (1 : UGroup N).val = 1 := rfl
    change ((1 : UGroup N).val *
      basisOffDiagCore (1 : UGroup N) E_diag ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩ *
      star (1 : UGroup N).val) x₀ x₁ = 0
    rw [h1val, star_one, one_mul, mul_one]
    dsimp [basisOffDiagCore]
    rw [star_one, one_mul, mul_one, hHu0]
    split_ifs <;> simp
  -- Decompose `V_chain = A + B` where `A = X_0 X_1` and `B = X_2`.
  let A : Register N := finitePauliMatrix (couplingWord 0 (0, 0))
  let B : Register N := finitePauliMatrix (onsiteWord s₂ 0)
  have hV_eq : V_chain = A + B := by
    dsimp [V_chain]
    rw [pathHamiltonian_eq_sum]
    let lA : PathLabel n := .inr (0, (0, 0))
    let lB : PathLabel n := .inl (s₂, 0)
    have hne_AB : lA ≠ lB := by simp [lA, lB]
    rw [← Finset.sum_subset (Finset.subset_univ ({lA, lB} : Finset (PathLabel n))),
      Finset.sum_pair hne_AB]
    · have huA : u_ent lA = 1 := by simp [u_ent, lA]
      have huB : u_ent lB = 1 := by simp [u_ent, lB]
      rw [huA, huB, Complex.ofReal_one, one_smul, one_smul]
      rfl
    · intro l _ hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      have hu0 : u_ent l = 0 := by simp [u_ent, lA, lB, hl.1, hl.2]
      rw [hu0, Complex.ofReal_zero, zero_smul]
  -- Intermediate states `x_01` (flips `0, 1`) and `x_2` (flips `2`).
  let x_01 : Config N := fun s => decide (s.val < 2)
  let x_2 : Config N := fun s => decide (s.val = 2)
  have hx01_ne_x2 : x_01 ≠ x_2 := fun h => by
    have hv := congrFun h s₀; simp [x_01, x_2, s₀] at hv
  -- Helper: `finitePauliMatrix` of a pure-`X` word flips its support!
  have hX_entry (S : Fin N → Bool) (P : Fin N → Option (Fin 3))
      (hP : ∀ s, P s = if S s then some 0 else none) (x y : Config N) :
      finitePauliMatrix P x y = if y = (fun s => xor (x s) (S s)) then 1 else 0 := by
    unfold finitePauliMatrix
    by_cases hy : y = fun s => xor (x s) (S s)
    · subst hy
      rw [if_pos rfl]
      refine Finset.prod_eq_one fun s _ => ?_
      rw [hP s]
      cases x s <;> cases S s <;> simp [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
    · rw [if_neg hy]
      obtain ⟨s, hs⟩ := Function.ne_iff.mp hy
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [hP s]
      cases hx : x s <;> cases hS : S s <;> cases hy_s : y s <;>
        simp_all [boolPauliOptionEntry, boolPauliOption, finiteQubitPauli]
  have hA_word (s : Fin N) : couplingWord (0 : Fin (n + 1)) (0, 0) s =
      if decide (s.val < 2) then some 0 else none := by
    by_cases h0 : s = (0 : Fin (n + 1)).castSucc
    · subst h0; simp [couplingWord]
    · by_cases h1 : s = (0 : Fin (n + 1)).succ
      · subst h1
        have hne : (0 : Fin (n + 1)).succ ≠ (0 : Fin (n + 1)).castSucc :=
          (0 : Fin (n + 1)).castSucc_lt_succ.ne'
        simp [couplingWord, hne]
      · have hv0 : s.val ≠ 0 := fun hv => h0 (Fin.ext (by simpa using hv))
        have hv1 : s.val ≠ 1 := fun hv => h1 (Fin.ext (by simpa using hv))
        have hnot2 : ¬ s.val < 2 := by omega
        simp [couplingWord, h0, h1, hnot2]
  have hB_word (s : Fin N) : onsiteWord s₂ 0 s =
      if decide (s.val = 2) then some 0 else none := by
    by_cases hs : s = s₂
    · subst hs; simp [onsiteWord, s₂]
    · have hv2 : s.val ≠ 2 := fun hv => hs (Fin.ext hv)
      simp [onsiteWord, hs, hv2]
  have hA_apply (x y : Config N) :
      A x y = if y = (fun s => xor (x s) (decide (s.val < 2))) then 1 else 0 :=
    hX_entry _ _ hA_word x y
  have hB_apply (x y : Config N) :
      B x y = if y = (fun s => xor (x s) (decide (s.val = 2))) then 1 else 0 :=
    hX_entry _ _ hB_word x y
  -- Energy differences on `S₃ = {s₀, s₁, s₂}`:
  let S₃ : Finset (Fin N) := {s₀, s₁, s₂}
  have hE_diff (y z : Config N) (hyz : ∀ s : Fin N, 3 ≤ s.val → y s = z s) :
      E_diag y - E_diag z =
        ((if y s₀ then 1 else -1) - (if z s₀ then 1 else -1)) * 1 +
        ((if y s₁ then 1 else -1) - (if z s₁ then 1 else -1)) * 2 +
        ((if y s₂ then 1 else -1) - (if z s₂ then 1 else -1)) * 4 := by
    dsimp [E_diag]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ S₃)]
    · rw [Finset.sum_insert (by simp [hs01, hs02]), Finset.sum_pair hs12]
      simp [s₀, s₁, s₂]; ring
    · intro s _ hs
      have hge3 : 3 ≤ s.val := by
        by_contra hlt3
        apply hs
        simp only [S₃, Finset.mem_insert, Finset.mem_singleton]
        rcases (show s.val = 0 ∨ s.val = 1 ∨ s.val = 2 by omega) with h0 | h1 | h2
        · exact Or.inl (Fin.ext h0)
        · exact Or.inr (Or.inl (Fin.ext h1))
        · exact Or.inr (Or.inr (Fin.ext h2))
      rw [hyz s hge3]; ring
  have hE_10 : E_diag x₁ - E_diag x₀ = 14 := by
    rw [hE_diff x₁ x₀ (fun s hs => by have : ¬ s.val < 3 := by omega; simp [x₁, x₀, this])]
    simp [x₁, x₀, s₀, s₁, s₂]; norm_num
  have hE_1_01 : E_diag x₁ - E_diag x_01 = 8 := by
    rw [hE_diff x₁ x_01 (fun s hs => by
      have h3 : ¬ s.val < 3 := by omega
      have h2 : ¬ s.val < 2 := by omega
      simp [x₁, x_01, h3, h2])]
    simp [x₁, x_01, s₀, s₁, s₂]; norm_num
  have hE_1_2 : E_diag x₁ - E_diag x_2 = 6 := by
    rw [hE_diff x₁ x_2 (fun s hs => by
      have h3 : ¬ s.val < 3 := by omega
      have h2 : s.val ≠ 2 := by omega
      simp [x₁, x_2, h3, h2])]
    simp [x₁, x_2, s₀, s₁, s₂]; norm_num
  -- Part 2: `secondOrderDysonOffDiag E_diag V_chain x₀ x₁ = 1 / 48`!
  have hdyson : secondOrderDysonOffDiag E_diag V_chain x₀ x₁ = (1 / 48 : ℂ) := by
    unfold secondOrderDysonOffDiag
    have hprod_c (c : Config N) :
        V_chain x₀ c * V_chain c x₁ = if c = x_01 ∨ c = x_2 then 1 else 0 := by
      rw [hV_eq, Matrix.add_apply, Matrix.add_apply, hA_apply x₀ c, hB_apply x₀ c,
        hA_apply c x₁, hB_apply c x₁]
      have hx0_A : (fun s : Fin N => xor (x₀ s) (decide (s.val < 2))) = x_01 := by
        funext s; simp [x₀, x_01]
      have hx0_B : (fun s : Fin N => xor (x₀ s) (decide (s.val = 2))) = x_2 := by
        funext s; simp [x₀, x_2]
      rw [hx0_A, hx0_B]
      by_cases hc01 : c = x_01
      · subst hc01
        have h1 : x₁ ≠ fun s : Fin N => xor (x_01 s) (decide (s.val < 2)) := fun h => by
          have hv := congrFun h s₀; simp [x₁, x_01, s₀] at hv
        have h2 : x₁ = fun s : Fin N => xor (x_01 s) (decide (s.val = 2)) := by
          funext s; dsimp [x₁, x_01]
          by_cases hs2 : s.val = 2
          · simp [hs2]
          · by_cases hs_lt : s.val < 2
            · have : s.val < 3 := by omega
              simp [hs2, hs_lt, this]
            · have : ¬ s.val < 3 := by omega
              simp [hs2, hs_lt, this]
        simp [hx01_ne_x2, h1, h2]
      · by_cases hc2 : c = x_2
        · subst hc2
          have h1 : x₁ = fun s : Fin N => xor (x_2 s) (decide (s.val < 2)) := by
            funext s; dsimp [x₁, x_2]
            by_cases hs2 : s.val = 2
            · simp [hs2]
            · by_cases hs_lt : s.val < 2
              · have : s.val < 3 := by omega
                simp [hs2, hs_lt, this]
              · have : ¬ s.val < 3 := by omega
                simp [hs2, hs_lt, this]
          have h2 : x₁ ≠ fun s : Fin N => xor (x_2 s) (decide (s.val = 2)) := fun h => by
            have hv := congrFun h s₀; simp [x₁, x_2, s₀] at hv
          simp [hc01, h1, h2]
        · simp [hc01, hc2]
    have hmem_01 : x_01 ∈ Finset.univ.filter (fun c : Config N => E_diag c ≠ E_diag x₁) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      linarith only [hE_1_01]
    have hmem_2 : x_2 ∈ Finset.univ.filter (fun c : Config N => E_diag c ≠ E_diag x₁) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      linarith only [hE_1_2]
    have hsub_pair : ({x_01, x_2} : Finset (Config N)) ⊆
        Finset.univ.filter (fun c : Config N => E_diag c ≠ E_diag x₁) := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact hmem_01
      · rw [Finset.mem_singleton.mp hc']; exact hmem_2
    rw [← Finset.sum_subset hsub_pair]
    · rw [Finset.sum_pair hx01_ne_x2, hprod_c x_01, hprod_c x_2,
        if_pos (Or.inl rfl), if_pos (Or.inr rfl), hE_10, hE_1_01, hE_1_2]
      norm_num
    · intro c _ hc_not
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc_not
      rw [hprod_c c, if_neg hc_not, zero_div]
  -- Part 3: `unitaryEvolution V_chain (π / 4) ∉ Set.range prodLocalMatrix`!
  have hnot_prod : unitaryEvolution V_chain (Real.pi / 4) ∉ Set.range (@prodLocalMatrix N) := by
    rintro ⟨R, hR_eq⟩
    let _ : NormedAlgebra ℚ (Register N) := .restrictScalars ℚ ℂ (Register N)
    let x_0 : Config N := fun s => decide (s.val = 0)
    let x_1 : Config N := fun s => decide (s.val = 1)
    -- Every `prodLocalMatrix R` has zero `2 × 2` minor on `{x₀, x_0, x_1, x_01}`!
    have hminor_prod :
        prodLocalMatrix R x₀ x₀ * prodLocalMatrix R x_01 x₀ -
          prodLocalMatrix R x_0 x₀ * prodLocalMatrix R x_1 x₀ = 0 := by
      let pair01 : Finset (Fin N) := {s₀, s₁}
      have hsplit (y : Config N) (hy : ∀ s ∈ pair01ᶜ, y s = false) :
          prodLocalMatrix R y x₀ =
            R s₀ (y s₀) false * R s₁ (y s₁) false *
              ∏ s ∈ pair01ᶜ, R s false false := by
        unfold prodLocalMatrix
        rw [← Finset.prod_mul_prod_compl pair01, Finset.prod_pair hs01]
        congr 1
        refine Finset.prod_congr rfl fun s hs => by rw [hy s hs]; rfl
      have hout (y : Config N) (hy : ∀ s : Fin N, 2 ≤ s.val → y s = false) :
          ∀ s ∈ pair01ᶜ, y s = false := by
        intro s hs
        simp only [pair01, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hs
        have hge2 : 2 ≤ s.val := by
          by_contra hlt2
          rcases (show s.val = 0 ∨ s.val = 1 by omega) with h0 | h1
          · exact hs.1 (Fin.ext h0)
          · exact hs.2 (Fin.ext h1)
        exact hy s hge2
      rw [hsplit x₀ (hout x₀ fun _ _ => rfl),
        hsplit x_01 (hout x_01 fun s hs => by have : ¬ s.val < 2 := by omega; simp [x_01, this]),
        hsplit x_0 (hout x_0 fun s hs => by have : s.val ≠ 0 := by omega; simp [x_0, this]),
        hsplit x_1 (hout x_1 fun s hs => by have : s.val ≠ 1 := by omega; simp [x_1, this])]
      simp only [x₀, x_01, x_0, x_1, s₀, s₁, Nat.zero_lt_two, Nat.one_lt_two, decide_true,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, decide_false]
      ring
    -- Compute `unitaryEvolution (A + B) (π / 4)` via commuting `A` and `B`!
    have hAB_comm : Commute A B := by
      change A * B = B * A
      dsimp [A, B]
      rw [finitePauliMatrix_mul, finitePauliMatrix_mul]
      have hlbl : (fun s => optMul (couplingWord 0 (0, 0) s) (onsiteWord s₂ 0 s)) =
          fun s => optMul (onsiteWord s₂ 0 s) (couplingWord 0 (0, 0) s) :=
        funext fun _ => optMul_comm _ _
      have hph1 : ∀ s : Fin N, optPhase (couplingWord 0 (0, 0) s) (onsiteWord s₂ 0 s) = 1 := by
        intro s; rw [hA_word s, hB_word s]
        by_cases h : s.val < 2
        · have hv2 : s.val ≠ 2 := by omega
          simp [h, hv2, optPhase]
        · simp [h, optPhase]
      have hph2 : ∀ s : Fin N, optPhase (onsiteWord s₂ 0 s) (couplingWord 0 (0, 0) s) = 1 := by
        intro s; rw [hA_word s, hB_word s]
        by_cases h : s.val = 2
        · have hnot : ¬ s.val < 2 := by omega
          simp [h, hnot, optPhase_none_right]
        · simp [h, optPhase]
      rw [hlbl, Finset.prod_eq_one fun s _ => hph1 s, Finset.prod_eq_one fun s _ => hph2 s]
    have hexp_split : unitaryEvolution V_chain (Real.pi / 4) =
        unitaryEvolution A (Real.pi / 4) * unitaryEvolution B (Real.pi / 4) := by
      rw [hV_eq]; unfold unitaryEvolution
      rw [smul_add, smul_add, NormedSpace.exp_add_of_commute
        (((hAB_comm.smul_left (-Complex.I)).smul_right (-Complex.I)).smul_left (Real.pi / 4) |>.smul_right (Real.pi / 4))]
    have hexp_inv {X : Register N} (hX : X * X = 1) :
        unitaryEvolution X (Real.pi / 4) =
          ((1 / Real.sqrt 2 : ℝ) : ℂ) • (1 : Register N) +
            ((-Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ))) • X := by
      unfold unitaryEvolution
      have hneg_sq : ((-Complex.I) • X) * ((-Complex.I) • X) = -1 := by
        rw [smul_mul_smul_comm, hX, smul_one_eq_coe, mul_neg, neg_mul, neg_neg, Complex.I_mul_I]
        simp
      have harg : (Real.pi / 4) • ((-Complex.I) • X) =
          ((Real.pi / 4 : ℝ) : ℂ) • ((-Complex.I) • X) := Complex.coe_smul _ _
      rw [harg, _root_.HTGeometry.exp_of_mul_self_eq_neg_sq_smul_one ((-Complex.I) • X) (Real.pi / 4)]
      · have hsinc : Real.sinc (Real.pi / 4) * (Real.pi / 4) = Real.sin (Real.pi / 4) := by
          have hne : (Real.pi / 4 : ℝ) ≠ 0 := by linarith only [Real.pi_pos]
          rw [Real.sinc_of_ne_zero hne, div_mul_cancel₀ _ hne]
        rw [smul_smul, ← Complex.ofReal_mul, hsinc, Real.cos_pi_div_four, Real.sin_pi_div_four,
          one_div, one_div, smul_smul, mul_comm _ (-Complex.I)]
      · rw [smul_mul_smul_comm, hneg_sq, smul_neg, ← neg_smul, pow_two]
    have hUA := hexp_inv (finitePauliMatrix_mul_self (couplingWord 0 (0, 0)))
    have hUB := hexp_inv (finitePauliMatrix_mul_self (onsiteWord s₂ 0))
    let c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
    have hc_sq : c * c = (1 / 2 : ℂ) := by
      dsimp [c]; rw [← Complex.ofReal_mul, div_mul_div_comm, one_mul, ← sq,
        Real.sq_sqrt two_pos.le]; norm_num
    -- Evaluate `(UA * UB) y x₀` for any `y` with `y s₂ = false`:
    have heval_col0 (y : Config N) (hys₂ : y s₂ = false) :
        (unitaryEvolution A (Real.pi / 4) * unitaryEvolution B (Real.pi / 4)) y x₀ =
          c * unitaryEvolution A (Real.pi / 4) y x₀ := by
      rw [Matrix.mul_apply, hUB]
      have hUB_col (z : Config N) :
          (c • (1 : Register N) + (-Complex.I * c) • B) z x₀ =
            if z = x₀ then c else if z = x_2 then -Complex.I * c else 0 := by
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          hB_apply z x₀]
        have hsymm_B : (x₀ = fun s => xor (z s) (decide (s.val = 2))) ↔ z = x_2 := by
          constructor
          · intro h; funext s
            have hs := congrFun h s
            dsimp [x₀, x_2] at hs ⊢
            cases z s <;> cases decide (s.val = 2) <;> simp_all
          · rintro rfl; funext s; dsimp [x₀, x_2]; cases decide (s.val = 2) <;> simp
        rw [if_congr hsymm_B rfl rfl]
        have hx0_ne_x2 : x₀ ≠ x_2 := fun h => by
          have hv := congrFun h s₂; simp [x₀, x_2, s₂] at hv
        by_cases hz0 : z = x₀
        · subst hz0; simp [hx0_ne_x2]
        · by_cases hz2 : z = x_2
          · subst hz2; simp [hz0]
          · simp [hz0, hz2]
      simp_rw [hUB_col]
      have hx0_ne_x2 : x₀ ≠ x_2 := fun h => by
        have hv := congrFun h s₂; simp [x₀, x_2, s₂] at hv
      rw [← Finset.sum_subset (Finset.subset_univ ({x₀, x_2} : Finset (Config N))),
        Finset.sum_pair hx0_ne_x2]
      · simp only [↓reduceIte, hx0_ne_x2.symm]
        have hUA_x2 : unitaryEvolution A (Real.pi / 4) y x_2 = 0 := by
          rw [hUA, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
            hA_apply y x_2]
          have hy_ne : y ≠ x_2 := fun h => by
            have hv := congrFun h s₂; rw [hys₂] at hv; simp [x_2, s₂] at hv
          have hA_ne : x_2 ≠ fun s => xor (y s) (decide (s.val < 2)) := fun h => by
            have hv := congrFun h s₂
            have hnot2 : ¬ s₂.val < 2 := by simp [s₂]
            simp [x_2, s₂, hys₂, hnot2] at hv
          simp [hy_ne, hA_ne]
        rw [hUA_x2, zero_mul, add_zero, mul_comm]
      · intro z _ hz
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        simp [hz.1, hz.2]
    let U := unitaryEvolution V_chain (Real.pi / 4)
    have hU_00 : U x₀ x₀ = 1 / 2 := by
      dsimp [U]; rw [hexp_split, heval_col0 x₀ rfl, hUA]
      have hne : x₀ ≠ fun s : Fin N => xor (x₀ s) (decide (s.val < 2)) := fun h => by
        have hv := congrFun h s₀; simp [x₀, s₀] at hv
      simp [Matrix.add_apply, Matrix.smul_apply, hA_apply x₀ x₀, hne, smul_eq_mul, hc_sq]
    have hU_01_0 : U x_01 x₀ = -Complex.I / 2 := by
      dsimp [U]
      rw [hexp_split, heval_col0 x_01 (by simp [x_01, s₂]), hUA]
      have hne1 : x_01 ≠ x₀ := fun h => by
        have hv := congrFun h s₀; simp [x_01, x₀, s₀] at hv
      have heqA : x₀ = fun s : Fin N => xor (x_01 s) (decide (s.val < 2)) := by
        funext s; simp [x₀, x_01]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, if_neg hne1,
        hA_apply x_01 x₀, if_pos heqA, smul_eq_mul, mul_zero, zero_add, mul_one]
      calc c * (-Complex.I * c) = -Complex.I * (c * c) := by ring
        _ = -Complex.I / 2 := by rw [hc_sq]; ring
    have hU_0_0 : U x_0 x₀ = 0 := by
      dsimp [U]; rw [hexp_split, heval_col0 x_0 (by simp [x_0, s₂]), hUA]
      have hne1 : x_0 ≠ x₀ := fun h => by have hv := congrFun h s₀; simp [x_0, x₀, s₀] at hv
      have hneA : x₀ ≠ fun s : Fin N => xor (x_0 s) (decide (s.val < 2)) := fun h => by
        have hv := congrFun h s₁; simp [x₀, x_0, s₁] at hv
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hne1, hA_apply x_0 x₀, hneA]
    have hU_1_0 : U x_1 x₀ = 0 := by
      dsimp [U]; rw [hexp_split, heval_col0 x_1 (by simp [x_1, s₂]), hUA]
      have hne1 : x_1 ≠ x₀ := fun h => by have hv := congrFun h s₁; simp [x_1, x₀, s₁] at hv
      have hneA : x₀ ≠ fun s : Fin N => xor (x_1 s) (decide (s.val < 2)) := fun h => by
        have hv := congrFun h s₀; simp [x₀, x_1, s₀] at hv
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hne1, hA_apply x_1 x₀, hneA]
    have hminor_U : U x₀ x₀ * U x_01 x₀ - U x_0 x₀ * U x_1 x₀ = -Complex.I / 4 := by
      rw [hU_00, hU_01_0, hU_0_0, hU_1_0]; ring
    rw [hR_eq] at hminor_prod
    change U x₀ x₀ * U x_01 x₀ - U x_0 x₀ * U x_1 x₀ = 0 at hminor_prod
    rw [hminor_U] at hminor_prod
    have hI_ne : (-Complex.I / 4 : ℂ) ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by norm_num)
    exact hI_ne hminor_prod
  exact ⟨hkato_zero, hdyson, hnot_prod⟩

#print axioms polya_lagrange_derivChain_sublevel_le
#print axioms gaussian_pi_le_of_fiber_bound
#print axioms gaussian_higherDeriv_piecewise_anticoncentration
#print axioms order_N_exponential_anticoncentration_at_quadraticScale
#print axioms fixed_tenth_locking_of_higherDeriv_sublinearOrder
#print axioms activeBudget_union_order_threshold
#print axioms unitaryJet_isSelfAdjoint
#print axioms liminf_torusCriticalHeight_higherOrderUnitaryJet_ge
#print axioms holder_dini_collar_diam_le
#print axioms gaussian_holder_dini_collar_anticoncentration
#print axioms torusCriticalHeight_prodLocal_left_eq
#print axioms torusCriticalHeight_const_along_localUnitary_curve
#print axioms euler_shuffle_reciprocal_sum
#print axioms twoLocal_secondOrder_dyson_escapes_hammingThree_blindSpot

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
