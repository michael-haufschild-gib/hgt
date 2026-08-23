import GaloisForLFunctions.HTGeometry.AntiLownerSignSwitch
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Anti-Löwner collision bridge

`[LEAN-PROVED] [LITERATURE-FORMALIZATION] [NOVELTY UNVERIFIED]`

Formalizes the doubled-node collision stage in Audenaert's finite-order anti-Löwner theorem.
Finite sign switching, punctured divided-difference convergence, closedness of the positive cone,
and reflection parity combine to force both `K + L` and `K - L` positive semidefinite.  This file
contains no RH assumption and does not assert the squared-Euler anti-Löwner producer.
-/

open Filter
open scoped Matrix MatrixOrder Topology

namespace RHTower

noncomputable section

def reflectionDoubledBlock {ι : Type*} [DecidableEq ι]
    (K L : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks K L L K

theorem reflectionDoubledBlock_quadratic_even
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K L : Matrix ι ι ℝ) (v : ι → ℝ) :
    star (Sum.elim v v) ⬝ᵥ
        (reflectionDoubledBlock K L).mulVec (Sum.elim v v) =
      2 * (star v ⬝ᵥ (K + L).mulVec v) := by
  rw [show (reflectionDoubledBlock K L).mulVec (Sum.elim v v) =
      Sum.elim (K.mulVec v + L.mulVec v) (L.mulVec v + K.mulVec v) by
    rw [reflectionDoubledBlock, Matrix.fromBlocks_mulVec]
    rfl]
  rw [show star (Sum.elim v v) = Sum.elim (star v) (star v) by rfl]
  rw [sumElim_dotProduct_sumElim]
  simp only [dotProduct_add, Matrix.add_mulVec]
  ring

theorem reflectionDoubledBlock_quadratic_odd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K L : Matrix ι ι ℝ) (v : ι → ℝ) :
    star (Sum.elim v (-v)) ⬝ᵥ
        (reflectionDoubledBlock K L).mulVec (Sum.elim v (-v)) =
      2 * (star v ⬝ᵥ (K - L).mulVec v) := by
  rw [show (reflectionDoubledBlock K L).mulVec (Sum.elim v (-v)) =
      Sum.elim (K.mulVec v - L.mulVec v) (L.mulVec v - K.mulVec v) by
    rw [reflectionDoubledBlock, Matrix.fromBlocks_mulVec]
    change Sum.elim (K.mulVec v + L.mulVec (-v))
      (L.mulVec v + K.mulVec (-v)) = _
    rw [Matrix.mulVec_neg, Matrix.mulVec_neg]
    abel]
  rw [show star (Sum.elim v (-v)) = Sum.elim (star v) (-(star v)) by
    funext i
    rcases i with i | i <;> simp]
  rw [sumElim_dotProduct_sumElim]
  simp only [dotProduct_sub, neg_dotProduct, Matrix.sub_mulVec]
  ring

theorem reflectionDoubledBlock_posSemidef_imp_add_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K L : Matrix ι ι ℝ}
    (hK : K.IsHermitian) (hL : L.IsHermitian)
    (hblock : (reflectionDoubledBlock K L).PosSemidef) :
    (K + L).PosSemidef ∧ (K - L).PosSemidef := by
  constructor
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hK.add hL)
    intro v
    have h := hblock.dotProduct_mulVec_nonneg (Sum.elim v v)
    rw [reflectionDoubledBlock_quadratic_even] at h
    linarith
  · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hK.sub hL)
    intro v
    have h := hblock.dotProduct_mulVec_nonneg (Sum.elim v (-v))
    rw [reflectionDoubledBlock_quadratic_odd] at h
    linarith

theorem reflectionDoubledBlock_add_sub_posSemidef_of_tendsto
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} [l.NeBot]
    {A : α → Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} {K L : Matrix ι ι ℝ}
    (hK : K.IsHermitian) (hL : L.IsHermitian)
    (hA : ∀ᶠ a in l, (A a).PosSemidef)
    (hlim : Tendsto A l (𝓝 (reflectionDoubledBlock K L))) :
    (K + L).PosSemidef ∧ (K - L).PosSemidef := by
  exact reflectionDoubledBlock_posSemidef_imp_add_sub hK hL
    (GaloisForLFunctions.HilbertMetric.Matrix.PosSemidef.of_tendsto hA hlim)

def antiLownerMatrixAt {ι : Type*} (g : ℝ → ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  signedAntiLownerMatrix x (g ∘ x) (fun _ ↦ 1)

def loewnerDerivativeMatrixAt {ι : Type*} [DecidableEq ι]
    (g : ℝ → ℝ) (g' x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then g' i else (g (x i) - g (x j)) / (x i - x j)

theorem loewnerDerivativeMatrixAt_comm
    {ι : Type*} [DecidableEq ι]
    (g : ℝ → ℝ) (g' x : ι → ℝ) (i j : ι) :
    loewnerDerivativeMatrixAt g g' x i j =
      loewnerDerivativeMatrixAt g g' x j i := by
  simp only [loewnerDerivativeMatrixAt]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := Ne.symm hij
    rw [if_neg hij, if_neg hji]
    rw [show g (x j) - g (x i) = -(g (x i) - g (x j)) by ring,
      show x j - x i = -(x i - x j) by ring, div_neg, neg_div]
    simp

theorem antiLownerMatrixAt_isHermitian
    {ι : Type*} (g : ℝ → ℝ) (x : ι → ℝ) :
    (antiLownerMatrixAt g x).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply, star_id_of_comm, antiLownerMatrixAt]
  exact signedAntiLownerMatrix_comm x (g ∘ x) (fun _ ↦ 1) j i

theorem loewnerDerivativeMatrixAt_isHermitian
    {ι : Type*} [DecidableEq ι]
    (g : ℝ → ℝ) (g' x : ι → ℝ) :
    (loewnerDerivativeMatrixAt g g' x).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply, star_id_of_comm]
  exact loewnerDerivativeMatrixAt_comm g g' x j i

theorem tendsto_const_add_nhdsNE_real (a : ℝ) :
    Tendsto (fun t : ℝ => a + t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] a) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Tendsto (fun t : ℝ => a + t) (𝓝 (0 : ℝ)) (𝓝 (a + 0)) :=
      (continuous_const.add continuous_id).continuousAt
    simpa using hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
    intro h
    exact ht (by linarith)

theorem tendsto_crossDividedDifference
    {g : ℝ → ℝ} {x y d : ℝ} (hg : HasDerivAt g d y) :
    Tendsto (fun ε : ℝ => (g x - g (y + ε)) / (x - (y + ε)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (if x = y then d else (g x - g y) / (x - y))) := by
  by_cases hxy : x = y
  · subst x
    rw [if_pos rfl]
    have hslope := hg.tendsto_slope.comp (tendsto_const_add_nhdsNE_real y)
    convert hslope using 1
    funext ε
    simp [slope, div_eq_mul_inv]
    ring
  · rw [if_neg hxy]
    have hshift : Tendsto (fun ε : ℝ => y + ε) (𝓝[≠] (0 : ℝ)) (𝓝 y) :=
      (tendsto_const_add_nhdsNE_real y).mono_right nhdsWithin_le_nhds
    exact (tendsto_const_nhds.sub (hg.continuousAt.tendsto.comp hshift)).div
      (tendsto_const_nhds.sub hshift) (sub_ne_zero.mpr hxy)

def audenaertDoubledNodes {ι : Type*} (x : ι → ℝ) (ε : ℝ) : ι ⊕ ι → ℝ :=
  Sum.elim x (fun i => x i + ε)

def audenaertDoubledSign {ι : Type*} : ι ⊕ ι → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -1)

def audenaertSignedCollisionMatrix {ι : Type*}
    (g : ℝ → ℝ) (x : ι → ℝ) (ε : ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  signedAntiLownerMatrix (audenaertDoubledNodes x ε)
    (g ∘ audenaertDoubledNodes x ε) audenaertDoubledSign

theorem tendsto_audenaertSignedCollisionMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ℝ → ℝ) (g' x : ι → ℝ)
    (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x)
    (hderiv : ∀ i, HasDerivAt g (g' i) (x i)) :
    Tendsto (audenaertSignedCollisionMatrix g x) (𝓝[≠] (0 : ℝ))
      (𝓝 (reflectionDoubledBlock (antiLownerMatrixAt g x)
        (loewnerDerivativeMatrixAt g g' x))) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  rcases i with i | i <;> rcases j with j | j
  · exact tendsto_const_nhds
  · simp only [audenaertSignedCollisionMatrix, audenaertDoubledNodes,
      audenaertDoubledSign, reflectionDoubledBlock, signedAntiLownerMatrix,
      Matrix.fromBlocks_apply₁₂, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
      one_mul, neg_one_mul]
    have h := tendsto_crossDividedDifference
      (x := x i) (y := x j) (hg := hderiv j)
    convert h using 1
    · funext ε
      ring
    · congr 1
      by_cases hij : i = j
      · subst j
        simp [loewnerDerivativeMatrixAt]
      · simp [loewnerDerivativeMatrixAt, hij, hinj.ne hij]
  · have h := tendsto_crossDividedDifference
      (x := x j) (y := x i) (hg := hderiv i)
    simp only [audenaertSignedCollisionMatrix, audenaertDoubledNodes,
      audenaertDoubledSign, reflectionDoubledBlock, signedAntiLownerMatrix,
      Matrix.fromBlocks_apply₂₁, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
      one_mul, neg_one_mul]
    convert h using 1
    · funext ε
      ring
    · congr 1
      rw [loewnerDerivativeMatrixAt_comm g g' x i j]
      by_cases hij : j = i
      · subst j
        simp [loewnerDerivativeMatrixAt]
      · simp [loewnerDerivativeMatrixAt, hij, hinj.ne hij]
  · have hxi : Tendsto (fun ε : ℝ => x i + ε) (𝓝[≠] (0 : ℝ)) (𝓝 (x i)) :=
      (tendsto_const_add_nhdsNE_real (x i)).mono_right nhdsWithin_le_nhds
    have hxj : Tendsto (fun ε : ℝ => x j + ε) (𝓝[≠] (0 : ℝ)) (𝓝 (x j)) :=
      (tendsto_const_add_nhdsNE_real (x j)).mono_right nhdsWithin_le_nhds
    have hgi := (hderiv i).continuousAt.tendsto.comp hxi
    have hgj := (hderiv j).continuousAt.tendsto.comp hxj
    have hquot := (hgi.add hgj).div (hxi.add hxj)
      (ne_of_gt (add_pos (hx i) (hx j)))
    simp only [audenaertSignedCollisionMatrix, audenaertDoubledNodes,
      audenaertDoubledSign, reflectionDoubledBlock, antiLownerMatrixAt,
      signedAntiLownerMatrix, Matrix.fromBlocks_apply₂₂, Function.comp_apply,
      Sum.elim_inr, neg_one_mul, one_mul]
    convert hquot using 1
    funext ε
    simp only [Function.comp_apply, Pi.div_apply]
    rw [show -g (x i + ε) + -g (x j + ε) =
        -(g (x i + ε) + g (x j + ε)) by ring,
      show -(x i + ε) + -(x j + ε) =
        -((x i + ε) + (x j + ε)) by ring,
      neg_div_neg_eq]

theorem audenaertDoubledSign_sq {ι : Type*} :
    ∀ k : ι ⊕ ι, (audenaertDoubledSign k) ^ 2 = 1 := by
  rintro (i | i) <;> norm_num [audenaertDoubledSign]

theorem eventually_audenaertDoubledNodes_pos
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ k, 0 < audenaertDoubledNodes x ε k := by
  rw [eventually_all]
  intro k
  rcases k with i | i
  · exact Filter.Eventually.of_forall fun _ => hx i
  · have hshift : Tendsto (fun ε : ℝ => x i + ε) (𝓝[≠] (0 : ℝ)) (𝓝 (x i)) :=
      (tendsto_const_add_nhdsNE_real (x i)).mono_right nhdsWithin_le_nhds
    exact hshift.eventually (Ioi_mem_nhds (hx i))

theorem eventually_audenaertDoubledNodes_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hinj : Function.Injective x) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), Function.Injective (audenaertDoubledNodes x ε) := by
  rw [show (∀ᶠ ε in 𝓝[≠] (0 : ℝ), Function.Injective (audenaertDoubledNodes x ε)) ↔
      ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ a b,
        audenaertDoubledNodes x ε a = audenaertDoubledNodes x ε b → a = b by rfl]
  rw [eventually_all]
  intro a
  rw [eventually_all]
  intro b
  rcases a with i | i <;> rcases b with j | j
  · exact Filter.Eventually.of_forall fun _ h => congrArg Sum.inl (hinj h)
  · by_cases hij : i = j
    · subst j
      filter_upwards [self_mem_nhdsWithin] with ε hε
      intro heq
      exfalso
      have hε0 : ε ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hε
      apply hε0
      simp only [audenaertDoubledNodes, Sum.elim_inl, Sum.elim_inr] at heq
      linarith
    · have hshift : Tendsto (fun ε : ℝ => x j + ε) (𝓝[≠] (0 : ℝ)) (𝓝 (x j)) :=
        (tendsto_const_add_nhdsNE_real (x j)).mono_right nhdsWithin_le_nhds
      have hne := hshift.eventually_ne (hinj.ne hij).symm
      filter_upwards [hne] with ε hneε
      intro heq
      exact (hneε (by
        simp only [audenaertDoubledNodes, Sum.elim_inl, Sum.elim_inr] at heq
        exact heq.symm)).elim
  · by_cases hij : i = j
    · subst j
      filter_upwards [self_mem_nhdsWithin] with ε hε
      intro heq
      exfalso
      have hε0 : ε ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hε
      apply hε0
      simp only [audenaertDoubledNodes, Sum.elim_inl, Sum.elim_inr] at heq
      linarith
    · have hshift : Tendsto (fun ε : ℝ => x i + ε) (𝓝[≠] (0 : ℝ)) (𝓝 (x i)) :=
        (tendsto_const_add_nhdsNE_real (x i)).mono_right nhdsWithin_le_nhds
      have hne := hshift.eventually_ne (hinj.ne hij)
      filter_upwards [hne] with ε hneε
      intro heq
      exact (hneε (by
        simp only [audenaertDoubledNodes, Sum.elim_inl, Sum.elim_inr] at heq
        exact heq)).elim
  · exact Filter.Eventually.of_forall fun _ h => congrArg Sum.inr (hinj (by
      simp only [audenaertDoubledNodes, Sum.elim_inr] at h
      linarith))

theorem eventually_audenaertSignedCollisionMatrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ℝ → ℝ) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x)
    (hg : ∀ t, 0 < t → 0 < g t)
    (hanti : ∀ z : ι ⊕ ι → ℝ, (∀ k, 0 < z k) → Function.Injective z →
      (antiLownerMatrixAt g z).PosSemidef) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), (audenaertSignedCollisionMatrix g x ε).PosSemidef := by
  filter_upwards [eventually_audenaertDoubledNodes_pos x hx,
    eventually_audenaertDoubledNodes_injective x hinj] with ε hpos hεinj
  apply (signedAntiLownerMatrix_posSemidef_iff_allPositive
    (audenaertDoubledNodes x ε) (g ∘ audenaertDoubledNodes x ε)
    audenaertDoubledSign audenaertDoubledSign_sq hpos
    (fun k => hg _ (hpos k)) hεinj).mpr
  simpa [antiLownerMatrixAt, audenaertSignedCollisionMatrix] using
    hanti (audenaertDoubledNodes x ε) hpos hεinj

/-- Audenaert's finite-order bridge.  Anti-Löwner positivity on doubled positive configurations
forces both reflection-parity combinations `K + L` and `K - L`, where `L` is the confluent
Löwner divided-difference matrix. -/
theorem antiLownerMatrixAt_posSemidef_imp_add_sub_loewnerDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ℝ → ℝ) (g' x : ι → ℝ)
    (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x)
    (hg : ∀ t, 0 < t → 0 < g t)
    (hderiv : ∀ i, HasDerivAt g (g' i) (x i))
    (hanti : ∀ z : ι ⊕ ι → ℝ, (∀ k, 0 < z k) → Function.Injective z →
      (antiLownerMatrixAt g z).PosSemidef) :
    ((antiLownerMatrixAt g x) + (loewnerDerivativeMatrixAt g g' x)).PosSemidef ∧
      ((antiLownerMatrixAt g x) - (loewnerDerivativeMatrixAt g g' x)).PosSemidef := by
  apply reflectionDoubledBlock_add_sub_posSemidef_of_tendsto
    (antiLownerMatrixAt_isHermitian g x)
    (loewnerDerivativeMatrixAt_isHermitian g g' x)
    (eventually_audenaertSignedCollisionMatrix_posSemidef g x hx hinj hg hanti)
  exact tendsto_audenaertSignedCollisionMatrix g g' x hx hinj hderiv

end

end RHTower
