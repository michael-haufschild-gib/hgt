import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheShortWindowsInheritThePolarization
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.ShortWindowsCarryAtMostOneNegativeSquare

/-!
# The cosh hyperplane inherits the polarization

Past the windows of length `3/5`, where Weil's form is nonnegative, CWS proves coercivity on a
hyperplane up to the length `log 2 + 1/50`, beyond the first prime: a smooth window test `H` of
such a length whose centred test has vanishing cosh moment `∫ H(u − A/2) cosh(u/2) du` has
`Q(H) ≥ ‖H‖²/1000` (`weilQuad_ge_of_coshOrthogonal`). On a family of smooth horizon windows `h_i`
the cosh moments `ℓ_i` of the synthesized tests `H_i = e^{y/2} h_i` cut out the **cosh
hyperplane** `Σ_i ℓ_i x_i = 0` of coefficient vectors. Then:

* **Weil's Gram matrix is nonnegative on the cosh hyperplane**
  (`hermQuad_weilWindowGram_nonneg_of_cosh`), so the pencil `P_K = κW(H) + (βJ/K)A(H)` is positive
  definite there at every multiple (`pencilGram_isPosDefOn_coshHyperplane`): mechanism B holds on a
  hyperplane of codimension one.
* **The pencil has at most one negative square** (`hermNegIndex_pencilGram_le_one`).
* **The complete family inherits it** (`eventually_isPosDefOn_coshHyperplane`): along the critical
  curve the Gram matrix of the complete family is eventually positive definite on the cosh
  hyperplane (positive definiteness on a subspace is open, `eventually_isPosDefOn_of_tendsto`).
* **The window index is at most one** (`eventually_hermNegIndex_horizonGram_le_one`): along the
  critical curve the Gram matrix of the complete family on every linearly independent family of
  smooth windows of length `< log 2 + 1/50` eventually has at most one negative square.

The integer of mechanism C thus carries a structural bound `≤ 1` on the windows of the first
prime, and the only direction that can carry a negative square is transverse to the cosh
hyperplane, the even direction of the pole moment.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell CohomologyOfWindowsOfSpecZ
  ArithmeticCriticalityTheory

variable {φ : ℝ → ℝ} {A : ℝ} {κ : Type*} [Fintype κ] [DecidableEq κ]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### Inertia against a positive subspace -/

omit [DecidableEq κ] in
/-- A form positive definite on `U` has at most `card − dim U` negative squares. -/
theorem hermNegIndex_add_finrank_le {H : Matrix κ κ ℂ} {U : Submodule ℂ (κ → ℂ)}
    (hU : IsPosDefOn H U) : hermNegIndex H + Module.finrank ℂ U ≤ Fintype.card κ := by
  obtain ⟨W, hWr, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  have hdis : W ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have h1 := hW x (Submodule.mem_inf.mp hx).1 hx0
    have h2 := hU x (Submodule.mem_inf.mp hx).2 hx0
    rw [hermQuad_neg] at h1
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W U
  rw [hdis, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_le (W ⊔ U)
  rw [Module.finrank_fintype_fun_eq_card] at hle
  unfold hermNegIndex
  omega

omit [DecidableEq κ] in
/-- `ind₋ + ind₊ ≤ card` for every matrix. -/
theorem hermNegIndex_add_hermPosIndex_le (H : Matrix κ κ ℂ) :
    hermNegIndex H + hermPosIndex H ≤ Fintype.card κ := by
  obtain ⟨W, hWr, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex H
  have := hermNegIndex_add_finrank_le hW
  omega

omit [DecidableEq κ] in
/-- The form of a compression: `hermQuad (Bᴴ M B) y = hermQuad M (B y)`. -/
theorem hermQuad_compress {r : Type*} [Fintype r] (M : Matrix κ κ ℂ) (B : Matrix κ r ℂ)
    (y : r → ℂ) : hermQuad (Bᴴ * M * B) y = hermQuad M (B *ᵥ y) := by
  unfold hermQuad
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

omit [DecidableEq κ] in
/-- **Positive definiteness on a subspace is open**: if Hermitian matrices `H_n → H₀` entrywise
and `H₀` is positive definite on `U`, then eventually every `H_n` is positive definite on `U`. -/
theorem eventually_isPosDefOn_of_tendsto {H : ℕ → Matrix κ κ ℂ} {H₀ : Matrix κ κ ℂ}
    (hH₀ : H₀.IsHermitian) {U : Submodule ℂ (κ → ℂ)} (hU : IsPosDefOn H₀ U)
    (hH : ∀ a b, Tendsto (fun n => H n a b) atTop (𝓝 (H₀ a b))) :
    ∀ᶠ n in atTop, IsPosDefOn (H n) U := by
  classical
  set b := Module.finBasis ℂ U
  set B : Matrix κ (Fin (Module.finrank ℂ U)) ℂ := fun i j => (b j : κ → ℂ) i with hB
  have hBy : ∀ y, B *ᵥ y = ((∑ j, y j • b j : U) : κ → ℂ) := fun y => by
    funext i
    simp only [Matrix.mulVec, dotProduct, hB, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hBne : ∀ y, y ≠ 0 → B *ᵥ y ≠ 0 := by
    intro y hy h0
    rw [hBy] at h0
    have h1 : (∑ j, y j • b j : U) = 0 := Subtype.ext h0
    have := (Fintype.linearIndependent_iff.mp b.linearIndependent) y h1
    exact hy (funext this)
  have hBmem : ∀ y, B *ᵥ y ∈ U := fun y => by rw [hBy]; exact Submodule.coe_mem _
  have hcH : (Bᴴ * H₀ * B).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hH₀.eq, Matrix.mul_assoc]
  have hcpos : ∀ y, y ≠ 0 → 0 < hermQuad (Bᴴ * H₀ * B) y := fun y hy => by
    rw [hermQuad_compress]
    exact hU _ (hBmem y) (hBne y hy)
  have hclim : ∀ a c, Tendsto (fun n => (Bᴴ * H n * B) a c) atTop (𝓝 ((Bᴴ * H₀ * B) a c)) := by
    intro a c
    simp only [Matrix.mul_apply]
    refine tendsto_finsetSum _ fun l _ => ?_
    refine Tendsto.mul_const _ (tendsto_finsetSum _ fun k _ => (hH k l).const_mul _)
  have hev := eventually_hermQuad_pos_of_tendsto hcH hcpos hclim
  filter_upwards [hev] with n hn
  intro x hx hx0
  set y := b.repr ⟨x, hx⟩ with hy
  have hxy : B *ᵥ (fun j => y j) = x := by
    rw [hBy]
    have := b.sum_repr ⟨x, hx⟩
    rw [← hy] at this
    rw [this]
  have hy0 : (fun j => y j) ≠ 0 := by
    intro h0
    apply hx0
    rw [← hxy, h0, Matrix.mulVec_zero]
  have := hn _ hy0
  rwa [hermQuad_compress, hxy] at this

/-! ### The cosh hyperplane -/

/-- The cosh moment of a window: `ℓ(h) = ∫ H(u − A/2) cosh(u/2) du`, `H = e^{y/2} h`. -/
def coshMoment (A : ℝ) (h : ℝ → ℝ) : ℝ := evenPoleMoment (centred A (halfWeight h))

/-- The linear functional `x ↦ Σ_i ℓ_i x_i` of a family of moments. -/
def momentFunctional (ℓ : κ → ℝ) : (κ → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, (ℓ i : ℂ) * x i
  map_add' x y := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The cosh hyperplane of a family of windows. -/
def coshHyperplane (A : ℝ) (h : κ → ℝ → ℝ) : Submodule ℂ (κ → ℂ) :=
  LinearMap.ker (momentFunctional fun i => coshMoment A (h i))

omit [DecidableEq κ] in
theorem mem_coshHyperplane {h : κ → ℝ → ℝ} {x : κ → ℂ} :
    x ∈ coshHyperplane A h ↔ ∑ i, (coshMoment A (h i) : ℂ) * x i = 0 :=
  LinearMap.mem_ker

omit [DecidableEq κ] in
/-- The cosh hyperplane has codimension at most one. -/
theorem card_le_finrank_coshHyperplane_add_one (h : κ → ℝ → ℝ) :
    Fintype.card κ ≤ Module.finrank ℂ (coshHyperplane A h) + 1 := by
  set f := momentFunctional fun i => coshMoment A (h i)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  have hr : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have e : coshHyperplane A h = LinearMap.ker f := rfl
  rw [e]
  omega

omit [DecidableEq κ] in
/-- The cosh moment of a combination of window tests is the combination of the moments. -/
theorem evenPoleMoment_centred_sum {H : κ → ℝ → ℝ} (hH : ∀ i, IsWindowTest A (H i)) (y : κ → ℝ) :
    evenPoleMoment (centred A fun u => ∑ i, y i * H i u) =
      ∑ i, y i * evenPoleMoment (centred A (H i)) := by
  have hc : Continuous fun x : ℝ => Real.cosh (x / 2) := by fun_prop
  have hint : ∀ i, Integrable fun x => centred A (H i) x * Real.cosh (x / 2) := fun i =>
    (((hH i).continuous.comp (continuous_sub_right _)).mul hc).integrable_of_hasCompactSupport
      (((hH i).hasCompactSupport.comp_homeomorph (Homeomorph.subRight (A / 2))).mul_right)
  unfold evenPoleMoment
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (hint i).const_mul _]
  congr 1
  funext x
  simp only [centred, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Weil's form on the cosh hyperplane -/

omit [DecidableEq κ] in
/-- **Weil's Gram matrix is nonnegative on the cosh hyperplane** for smooth windows of length
`A < log 2 + 1/50`. -/
theorem hermQuad_weilWindowGram_nonneg_of_cosh (hA0 : 0 ≤ A) (hA : A < Real.log 2 + 1 / 50)
    {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) {x : κ → ℂ}
    (hx : x ∈ coshHyperplane A h) : 0 ≤ hermQuad (weilWindowGram φ h) x := by
  have hh2 : ∀ i, ContDiff ℝ 2 (h i) := fun i => (hh i).of_le (WithTop.coe_le_coe.mpr le_top)
  have hH : ∀ i, ContDiff ℝ 2 (halfWeight (h i)) := fun i => contDiff_halfWeight (hh2 i)
  have hHs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (halfWeight (h i)) := fun i =>
    (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul (hh i)
  have hHc : ∀ i, HasCompactSupport (halfWeight (h i)) := fun i =>
    hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))
  have hHv : ∀ i y, y ∉ Set.Icc (-A) 0 → halfWeight (h i) y = 0 := fun i =>
    halfWeight_eq_zero_of_window (hsupp i)
  have hW : ∀ i, IsWindowTest A (halfWeight (h i)) := fun i => ⟨hH i, hHv i⟩
  -- every real vector on the hyperplane gives a coercive window test
  have hQ : ∀ y : κ → ℝ, ∑ i, coshMoment A (h i) * y i = 0 →
      0 ≤ weilQuad (fun u => ∑ i, y i * halfWeight (h i) u) := by
    intro y hy
    have hF : IsWindowTest A (fun u => ∑ i, y i * halfWeight (h i) u) :=
      ⟨ContDiff.sum fun i _ => contDiff_const.mul (hH i), fun u hu => by simp [hHv _ u hu]⟩
    have hFs : ContDiff ℝ (⊤ : ℕ∞) (fun u => ∑ i, y i * halfWeight (h i) u) :=
      ContDiff.sum fun i _ => contDiff_const.mul (hHs i)
    have hC : evenPoleMoment (centred A fun u => ∑ i, y i * halfWeight (h i) u) = 0 := by
      rw [evenPoleMoment_centred_sum hW]
      rw [← hy]
      exact Finset.sum_congr rfl fun i _ => by unfold coshMoment; ring
    have h1 := weilQuad_ge_of_coshOrthogonal hA0 hA hF hFs hC
    have h2 : 0 ≤ ∫ u, (∑ i, y i * halfWeight (h i) u) ^ 2 :=
      integral_nonneg fun u => sq_nonneg _
    linarith
  have hx' := mem_coshHyperplane.mp hx
  have hre : ∑ i, coshMoment A (h i) * (x i).re = 0 := by
    have := congrArg Complex.re hx'
    simpa [Complex.re_sum, Complex.re_ofReal_mul] using this
  have him : ∑ i, coshMoment A (h i) * (x i).im = 0 := by
    have := congrArg Complex.im hx'
    simpa [Complex.im_sum, Complex.im_ofReal_mul] using this
  have hreal : ∀ i j, ((weilGram Λw fun i => cx (halfWeight (h i))) i j).im = 0 := by
    intro i j
    simp only [weilGram]
    rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (hH i) (hHc i) (hH j) (hHc j),
      Complex.ofReal_im]
  unfold weilWindowGram
  rw [HTGeometry.hermQuad_smul, hermQuad_eq_re_add_im hreal]
  rw [hermQuad_weilGram_ofReal hH hHv (fun i => (x i).re),
    hermQuad_weilGram_ofReal hH hHv (fun i => (x i).im)]
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := by
    have : (0 : ℝ) ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
    positivity
  exact mul_nonneg hκ (add_nonneg (hQ _ hre) (hQ _ him))

omit [DecidableEq κ] in
/-- **The pencil is positive definite on the cosh hyperplane** at every multiple `K > 0`. -/
theorem pencilGram_isPosDefOn_coshHyperplane (hA0 : 0 ≤ A) (hA : A < Real.log 2 + 1 / 50)
    {β J K : ℝ} (hβJ : 0 < β * J) (hK : 0 < K) {h : κ → ℝ → ℝ}
    (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i)) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hlin : LinearIndependent ℝ h) :
    IsPosDefOn (pencilGram φ β J K h) (coshHyperplane A h) := by
  have hh2 : ∀ i, ContDiff ℝ 2 (h i) := fun i => (hh i).of_le (WithTop.coe_le_coe.mpr le_top)
  intro x hx hx0
  rw [pencilGram_eq hh2 hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]
  have hW := hermQuad_weilWindowGram_nonneg_of_cosh (φ := φ) hA0 hA hh hsupp hx
  have hB : 0 < hermQuad (aliasGram β h) x := by
    have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hh2 hsupp hlin)).2 hx0
    simpa [hermQuad] using (Complex.lt_def.mp h1).1
  have hc : 0 < β * J / K := div_pos hβJ hK
  nlinarith

omit [DecidableEq κ] in
/-- **The pencil has at most one negative square** on smooth windows of length
`< log 2 + 1/50`. -/
theorem hermNegIndex_pencilGram_le_one (hA0 : 0 ≤ A) (hA : A < Real.log 2 + 1 / 50)
    {β J K : ℝ} (hβJ : 0 < β * J) (hK : 0 < K) {h : κ → ℝ → ℝ}
    (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i)) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hlin : LinearIndependent ℝ h) :
    hermNegIndex (pencilGram φ β J K h) ≤ 1 := by
  have h1 := hermNegIndex_add_finrank_le
    (pencilGram_isPosDefOn_coshHyperplane (φ := φ) hA0 hA hβJ hK hh hsupp hlin)
  have h2 := card_le_finrank_coshHyperplane_add_one (A := A) h
  omega

/-- **The window index is at most one below `log 2 + 1/50`.** For every profile with bulk limit
`s^β E₁(s) → J`, `βJ > 0`, and every linearly independent family of smooth horizon windows of
length `A < log 2 + 1/50`: along `c^{β+1}/log N → K > 0` the Gram matrix of the complete family on
the family eventually has at most one negative square. -/
theorem eventually_hermNegIndex_horizonGram_le_one (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β) (hβJ : 0 < β * J)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i)) (hA : 0 ≤ A)
    (hAl : A < Real.log 2 + 1 / 50) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hlin : LinearIndependent ℝ h) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, hermNegIndex (horizonGram φ h (c N) N) ≤ 1 := by
  have hh2 : ∀ i, ContDiff ℝ 2 (h i) := fun i => (hh i).of_le (WithTop.coe_le_coe.mpr le_top)
  set P := pencilGram φ β J K h with hP
  have hPH := pencilGram_isHermitian hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh2 hA hsupp hc1 hK hcrit
  have hlim := tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh2 hA hsupp hc1 hK hcrit
  -- lower semicontinuity of the positive index
  have hneg : (-P).IsHermitian := hPH.neg
  have hlim' : ∀ a b, Tendsto (fun N : ℕ => (-((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) :
      ℂ) • horizonGram φ h (c N) N)) a b) atTop (𝓝 ((-P) a b)) := fun a b => by
    simpa using (hlim a b).neg
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex hneg hlim'
  have hU := pencilGram_isPosDefOn_coshHyperplane (φ := φ) hA hAl hβJ hK hh hsupp hlin
  have hPpos : Module.finrank ℂ (coshHyperplane A h) ≤ hermPosIndex P := finrank_le_posIndex hU
  have hcard := card_le_finrank_coshHyperplane_add_one (A := A) h
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  set G := (((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) • horizonGram φ h (c N) N
  have e1 : hermNegIndex (-P) = hermPosIndex P := by rw [hermNegIndex, neg_neg]
  have e2 : hermNegIndex (-G) = hermPosIndex G := by rw [hermNegIndex, neg_neg]
  rw [e1, e2] at hN
  have hsum := hermNegIndex_add_hermPosIndex_le G
  have hGN : hermNegIndex G = hermNegIndex (horizonGram φ h (c N) N) :=
    hermNegIndex_ofReal_smul hs _
  omega

omit [DecidableEq κ] in
/-- **The cosh hyperplane inherits the polarization.** Under the same hypotheses, along the
critical curve the Gram matrix of the complete family is eventually positive definite on the cosh
hyperplane of the family. -/
theorem eventually_isPosDefOn_coshHyperplane (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 ≤ β) (hβJ : 0 < β * J)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : κ → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i)) (hA : 0 ≤ A)
    (hAl : A < Real.log 2 + 1 / 50) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hlin : LinearIndependent ℝ h) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, IsPosDefOn (horizonGram φ h (c N) N) (coshHyperplane A h) := by
  have hh2 : ∀ i, ContDiff ℝ 2 (h i) := fun i => (hh i).of_le (WithTop.coe_le_coe.mpr le_top)
  have hPH := pencilGram_isHermitian hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh2 hA hsupp hc1 hK hcrit
  have hlim := tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ hbulk hh2 hA hsupp hc1 hK hcrit
  have hU := pencilGram_isPosDefOn_coshHyperplane (φ := φ) hA hAl hβJ hK hh hsupp hlin
  have hev := eventually_isPosDefOn_of_tendsto hPH hU hlim
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx hx0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  have := hN x hx hx0
  rw [HTGeometry.hermQuad_smul] at this
  exact pos_of_mul_pos_right this hs.le

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
