import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheDysonFlowKeepsTheMesh
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.CollisionsBlowUpToHermiteProfiles
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheZeroNumberDropsOnlyAtCollisions
import GaloisForLFunctions.HTGeometry.HermitePerturbationRealRoots

/-!
# The Hermite mesh is pinched

The profile of a collision of order `k` is `Q_k = e^{−D²}σ^k`, and its roots `√2 y`, `He_k(y) = 0`, are a stationary configuration of the Dyson flow in self-similar variables: `2 Σ_{j ≠ i} 1/(y_i − y_j) = y_i`
(`dysonVelocity_hermite`), the Stieltjes relation. At a mesh pair the rate law gives `2g² ≥ 16/k`. So the least gap of the profile is pinched:

`16/k ≤ μ² ≤ 24/(k + 1)`    (`sq_sub_ge_profileRoots`, `exists_close_profileRoots`),

with equality on both sides at `k = 2`.

For the actual flow this is the local repulsion law at a collision. Just above a real zero of order `k` of `H_{t₀}`, every pair of real zeros near it satisfies `g² ≥ (16/k − ε)(t − t₀)` (`exists_gap_ge_near_collision`), and some pair satisfies `g² ≤ (24/(k + 1) + ε)(t − t₀)`
(`exists_close_zeros_forward`). So near a collision the central inequality holds exactly up to the factor `1/k` that its order forces.
-/

open Polynomial Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## The second derivative at a simple root -/

/-- `p″(y_i) = 2 p′(y_i) Σ_{j ≠ i} 1/(y_i − y_j)` for a product of linear factors with distinct roots. -/
theorem eval_derivative_derivative_prod {n : ℕ} {y : Fin n → ℝ} (hy : Function.Injective y) (i : Fin n) :
    (derivative (derivative (∏ j, (X - C (y j))))).eval (y i) =
      2 * (derivative (∏ j, (X - C (y j)))).eval (y i) * ∑ j ∈ Finset.univ.erase i, 1 / (y i - y j) := by
  classical
  set s := (Finset.univ : Finset (Fin n)).erase i with hs
  set q := ∏ j ∈ s, (X - C (y j)) with hq
  have hfac : ∏ j, (X - C (y j)) = (X - C (y i)) * q :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
  have hne (j : Fin n) (hj : j ∈ s) : y i - y j ≠ 0 :=
    sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hj).1 (hy h).symm
  have hq' : (derivative q).eval (y i) = q.eval (y i) * ∑ j ∈ s, 1 / (y i - y j) := by
    rw [hq, derivative_prod_finset, eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [derivative_X_sub_C, mul_one, eval_prod, eval_prod]
    have h0 : y i - y j = eval (y i) (X - C (y j)) := by simp
    have h1 : ∏ k ∈ s, eval (y i) (X - C (y k)) = (∏ k ∈ s.erase j, eval (y i) (X - C (y k))) * (y i - y j) := by
      rw [h0, Finset.prod_erase_mul _ _ hj]
    rw [h1]
    have := hne j hj
    field_simp
  rw [hfac]
  have hd1 : derivative ((X - C (y i)) * q) = q + (X - C (y i)) * derivative q := by
    rw [derivative_mul, derivative_X_sub_C, one_mul]
  have hd2 : derivative (q + (X - C (y i)) * derivative q) =
      derivative q + (derivative q + (X - C (y i)) * derivative (derivative q)) := by
    rw [derivative_add, derivative_mul, derivative_X_sub_C, one_mul]
  rw [hd1, hd2]
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  rw [hq']
  ring

/-! ## The Stieltjes relation -/

/-- The roots of `He_k`, in increasing order. -/
def hermiteRoot (k : ℕ) : Fin k → ℝ :=
  (gaussianDerivZeros k).orderEmbOfFin (by
    obtain ⟨hnd, hcard⟩ := realHermite_roots_nodup_card k
    rw [gaussianDerivZeros, Multiset.toFinset_card_of_nodup hnd, hcard])

theorem card_gaussianDerivZeros (k : ℕ) : (gaussianDerivZeros k).card = k := by
  obtain ⟨hnd, hcard⟩ := realHermite_roots_nodup_card k
  rw [gaussianDerivZeros, Multiset.toFinset_card_of_nodup hnd, hcard]

theorem hermiteRoot_strictMono (k : ℕ) : StrictMono (hermiteRoot k) :=
  ((gaussianDerivZeros k).orderEmbOfFin _).strictMono

theorem hermiteRoot_mem (k : ℕ) (i : Fin k) : hermiteRoot k i ∈ gaussianDerivZeros k :=
  Finset.orderEmbOfFin_mem _ _ i

theorem exists_hermiteRoot_eq {k : ℕ} {y : ℝ} (hy : y ∈ gaussianDerivZeros k) : ∃ i, hermiteRoot k i = y := by
  have h := Finset.range_orderEmbOfFin (gaussianDerivZeros k) (card_gaussianDerivZeros k)
  have hy' : y ∈ Set.range ((gaussianDerivZeros k).orderEmbOfFin (card_gaussianDerivZeros k)) := by
    rw [h]
    exact hy
  exact hy'

/-- `He_k` is the product of its linear factors. -/
theorem realHermite_eq_prod (k : ℕ) : realHermite k = ∏ j, (X - C (hermiteRoot k j)) := by
  classical
  have hs : (realHermite k).Splits := splits_hermiteReal k
  have hm : (realHermite k).Monic := by
    rw [Monic, realHermite, leadingCoeff_map_of_injective (RingHom.injective_int _), leadingCoeff_hermite]
    simp
  obtain ⟨hnd, -⟩ := realHermite_roots_nodup_card k
  have h1 := hs.eq_prod_roots_of_monic hm
  have h2 : (realHermite k).roots = (gaussianDerivZeros k).val := by
    rw [gaussianDerivZeros, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  rw [h2] at h1
  rw [h1]
  change ∏ a ∈ gaussianDerivZeros k, (X - C a) = _
  rw [← Finset.map_orderEmbOfFin_univ (gaussianDerivZeros k) (card_gaussianDerivZeros k), Finset.prod_map]
  rfl

/-- The differential equation `He_k″ = X He_k′ − k He_k`. -/
theorem derivative_derivative_realHermite (k : ℕ) :
    derivative (derivative (realHermite k)) = X * derivative (realHermite k) - C (k : ℝ) * realHermite k := by
  cases k with
  | zero =>
    simp [realHermite]
  | succ m =>
    have h1 : derivative (hermiteReal (m + 1)) = C ((m : ℝ) + 1) * hermiteReal m := derivative_hermiteReal_succ m
    have h2 : hermiteReal (m + 1) = X * hermiteReal m - C 1 * derivative (hermiteReal m) := hermiteReal_succ m
    change derivative (derivative (hermiteReal (m + 1))) = X * derivative (hermiteReal (m + 1)) -
      C ((m + 1 : ℕ) : ℝ) * hermiteReal (m + 1)
    rw [h1, derivative_C_mul]
    conv_rhs => rw [h2]
    push_cast
    simp only [map_add, C_1, map_natCast, one_mul]
    ring

/-- **The Stieltjes relation.** The roots of `He_k` are stationary in self-similar variables: `2 Σ_{j ≠ i} 1/(y_i − y_j) = y_i`. -/
theorem dysonVelocity_hermite {k : ℕ} (i : Fin k) : dysonVelocity (hermiteRoot k) i = hermiteRoot k i := by
  classical
  have hinj := (hermiteRoot_strictMono k).injective
  have hroot : (realHermite k).IsRoot (hermiteRoot k i) := by
    have h := hermiteRoot_mem k i
    rw [gaussianDerivZeros, Multiset.mem_toFinset] at h
    exact (mem_roots (realHermite_ne_zero k)).mp h
  obtain ⟨hnd, -⟩ := realHermite_roots_nodup_card k
  have hd := derivative_eval_ne_zero_of_roots_nodup (realHermite_ne_zero k) hnd hroot
  have hode := congrArg (eval (hermiteRoot k i)) (derivative_derivative_realHermite k)
  simp only [eval_sub, eval_mul, eval_X, eval_C, hroot.eq_zero, mul_zero, sub_zero] at hode
  have hprod := eval_derivative_derivative_prod hinj i
  rw [← realHermite_eq_prod k, hode] at hprod
  unfold dysonVelocity
  have h3 : (derivative (realHermite k)).eval (hermiteRoot k i) * hermiteRoot k i =
      (derivative (realHermite k)).eval (hermiteRoot k i) *
        (2 * ∑ j ∈ Finset.univ.erase i, 1 / (hermiteRoot k i - hermiteRoot k j)) := by
    rw [mul_comm, hprod]
    ring
  exact (mul_left_cancel₀ hd h3).symm

/-! ## The pinch -/

/-- **The lower bound of the pinch.** Any two roots of `He_k` have squared distance at least `8/k`. -/
theorem sq_sub_ge_hermiteRoot {k : ℕ} {i j : Fin k} (hij : i < j) :
    8 / (k : ℝ) ≤ (hermiteRoot k j - hermiteRoot k i) ^ 2 := by
  classical
  have hstrict := hermiteRoot_strictMono k
  set P := (Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2) with hP
  have hne : P.Nonempty := ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
  obtain ⟨p, hp, hmin⟩ := P.exists_min_image (fun p => hermiteRoot k p.2 - hermiteRoot k p.1) hne
  have hplt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hsep : ∀ a b : Fin k, a < b → hermiteRoot k p.2 - hermiteRoot k p.1 ≤ hermiteRoot k b - hermiteRoot k a :=
    fun a b hab => hmin (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
  have hrate := rate_ge_of_mesh_pair hstrict hplt hsep
  rw [dysonVelocity_hermite, dysonVelocity_hermite] at hrate
  have hg : 0 < hermiteRoot k p.2 - hermiteRoot k p.1 := sub_pos.mpr (hstrict hplt)
  have h1 := hsep i j hij
  have h2 : (hermiteRoot k p.2 - hermiteRoot k p.1) ^ 2 ≤ (hermiteRoot k j - hermiteRoot k i) ^ 2 :=
    pow_le_pow_left₀ hg.le h1 2
  have h3 : 16 / (k : ℝ) = 2 * (8 / (k : ℝ)) := by ring
  nlinarith only [hrate, h2, h3]

/-- **The pinch for the profile.** Any two roots of `Q_k` have squared distance at least `16/k`. -/
theorem sq_sub_ge_profileRoots {k : ℕ} {ρ ρ' : ℝ} (hρ : ρ ∈ profileRoots k) (hρ' : ρ' ∈ profileRoots k) (hne : ρ ≠ ρ') :
    16 / (k : ℝ) ≤ (ρ - ρ') ^ 2 := by
  classical
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hρ
  obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hρ'
  obtain ⟨i, rfl⟩ := exists_hermiteRoot_eq (k := k) (y := y) hy
  obtain ⟨j, rfl⟩ := exists_hermiteRoot_eq (k := k) (y := y') hy'
  have hij : i ≠ j := by
    rintro rfl
    exact hne rfl
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrew : (Real.sqrt 2 * hermiteRoot k i - Real.sqrt 2 * hermiteRoot k j) ^ 2 =
      2 * (hermiteRoot k j - hermiteRoot k i) ^ 2 := by
    rw [show Real.sqrt 2 * hermiteRoot k i - Real.sqrt 2 * hermiteRoot k j =
      Real.sqrt 2 * (hermiteRoot k i - hermiteRoot k j) by ring, mul_pow, hs2]
    ring
  rw [hrew]
  have h16 : 16 / (k : ℝ) = 2 * (8 / (k : ℝ)) := by ring
  rw [h16]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rcases lt_or_gt_of_ne hij with h | h
  · exact sq_sub_ge_hermiteRoot h
  · have := sq_sub_ge_hermiteRoot h
    rwa [show (hermiteRoot k i - hermiteRoot k j) ^ 2 = (hermiteRoot k j - hermiteRoot k i) ^ 2 by ring] at this

/-! ## The local law at an actual collision -/

/-- **The local repulsion law at a collision.** Just above a real zero of order `k`, any two real zeros near it satisfy `g² ≥ (16/k − ε)(t − t₀)`. -/
theorem exists_gap_ge_near_collision {s : ℝ} (hs : 0 < s) {x₀ : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hvan : ∀ i < k, iteratedDeriv i (riemannHeat s) x₀ = 0)
    (ha : iteratedDeriv k (riemannHeat s) x₀ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ q₁ > 0, ∀ q, 0 < q → q ≤ q₁ → ∀ y y' : ℝ, y < y' → |y - x₀| ≤ r → |y' - x₀| ≤ r →
      riemannHeat (s + q ^ 2) (y : ℂ) = 0 → riemannHeat (s + q ^ 2) (y' : ℂ) = 0 →
      (16 / (k : ℝ) - ε) * q ^ 2 ≤ (y' - y) ^ 2 := by
  classical
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [this]
  -- the multiplicity of the zero
  have h0 : riemannHeat s (x₀ : ℂ) = 0 := by
    have := hvan 0 (by omega)
    simpa using this
  have hm : zeroMult (riemannHeat s) (x₀ : ℂ) = k := by
    obtain ⟨hv, hne⟩ := iteratedDeriv_zeroMult_data hs.le (x₀ : ℂ)
    rcases lt_trichotomy (zeroMult (riemannHeat s) (x₀ : ℂ)) k with h | h | h
    · exact absurd (hvan _ h) hne
    · exact h
    · exact absurd (hv _ h) ha
  -- the separation of the roots
  set μ := Real.sqrt (16 / (k : ℝ)) with hμ
  have hμsq : μ ^ 2 = 16 / (k : ℝ) := Real.sq_sqrt (by positivity)
  have hμpos : 0 < μ := Real.sqrt_pos.mpr (by positivity)
  set ε₁ := min (μ / 4) (ε / (8 * μ + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := lt_min (by positivity) (by positivity)
  have hε₁1 : ε₁ ≤ μ / 4 := min_le_left _ _
  have hε₁2 : ε₁ ≤ ε / (8 * μ + 1) := min_le_right _ _
  have hsep (ρ ρ' : ℝ) (hρ : ρ ∈ profileRoots k) (hρ' : ρ' ∈ profileRoots k) (hne : ρ ≠ ρ') : μ ≤ |ρ - ρ'| := by
    have h1 := sq_sub_ge_profileRoots hρ hρ' hne
    rw [← hμsq, ← sq_abs (ρ - ρ')] at h1
    exact (sq_le_sq₀ hμpos.le (abs_nonneg _)).mp h1
  obtain ⟨q₁, hq₁, hnear⟩ := exists_zero_near_root_forward hs.le hvan ha hε₁pos
  obtain ⟨ε₀, hε₀, hlaw⟩ := exists_local_realZeroCount_at_point hs x₀ h0
  obtain ⟨δ, hδ, hcount⟩ := hlaw ε₀ hε₀ le_rfl
  rw [hm] at hcount
  set S := ∑ ρ ∈ profileRoots k, |ρ| + μ with hS
  have hSpos : 0 < S := by
    have : 0 ≤ ∑ ρ ∈ profileRoots k, |ρ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [hS]
    linarith only [this, hμpos]
  refine ⟨ε₀, hε₀, min q₁ (min (ε₀ / S) (Real.sqrt (δ / 2))),
    lt_min hq₁ (lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))), ?_⟩
  intro q hq hqle y y' hyy' hyr hy'r hy0 hy'0
  have hq1 : q ≤ q₁ := hqle.trans (min_le_left _ _)
  have hq2 : q ≤ ε₀ / S := hqle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hq3 : q ≤ Real.sqrt (δ / 2) := hqle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hqS : S * q ≤ ε₀ := by
    have := (le_div_iff₀ hSpos).mp hq2
    linarith only [this]
  have hq2δ : q ^ 2 < δ := by
    have := pow_le_pow_left₀ hq.le hq3 2
    rw [Real.sq_sqrt (by positivity)] at this
    linarith only [this, hδ]
  set t := s + q ^ 2 with ht
  have htpos : 0 < t := by positivity
  obtain ⟨-, hup, -⟩ := hcount t (by
    rw [ht, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    exact hq2δ)
  have hcnt := hup (by rw [ht]; nlinarith only [sq_nonneg q])
  -- the zeros following the roots
  have hfol := hnear q hq hq1
  choose! f hf using hfol
  have hfmem (ρ : ℝ) (hρ : ρ ∈ profileRoots k) : f ρ ∈ realZeroFinset t (x₀ - ε₀) (x₀ + ε₀) := by
    refine (mem_realZeroFinset htpos.le).mpr ⟨?_, (hf ρ hρ).2⟩
    have h1 := (abs_le.mp (hf ρ hρ).1)
    have h2 : |ρ| ≤ ∑ ρ ∈ profileRoots k, |ρ| :=
      Finset.single_le_sum (f := fun ρ => |ρ|) (fun _ _ => abs_nonneg _) hρ
    have h3 : q * |ρ| + ε₁ * q ≤ S * q := by
      rw [hS]
      nlinarith only [h2, hq, hε₁1, hμpos, mul_nonneg hq.le (sub_nonneg.mpr hε₁1)]
    have h4 : -(q * |ρ|) ≤ q * ρ := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le ρ) hq.le
      linarith only [this]
    have h5 : q * ρ ≤ q * |ρ| := mul_le_mul_of_nonneg_left (le_abs_self ρ) hq.le
    constructor <;> linarith only [h1.1, h1.2, h3, h4, h5, hqS]
  have hfsep (ρ ρ' : ℝ) (hρ : ρ ∈ profileRoots k) (hρ' : ρ' ∈ profileRoots k) (hne : ρ ≠ ρ') :
      q * (μ - 2 * ε₁) ≤ |f ρ - f ρ'| := by
    have h1 := hsep ρ ρ' hρ hρ' hne
    have h2 := (hf ρ hρ).1
    have h3 := (hf ρ' hρ').1
    have h4 : q * |ρ - ρ'| = |(f ρ - f ρ') - ((f ρ - (x₀ + q * ρ)) - (f ρ' - (x₀ + q * ρ')))| := by
      rw [show (f ρ - f ρ') - ((f ρ - (x₀ + q * ρ)) - (f ρ' - (x₀ + q * ρ'))) = q * (ρ - ρ') by ring,
        abs_mul, abs_of_pos hq]
    have h5 : |(f ρ - f ρ') - ((f ρ - (x₀ + q * ρ)) - (f ρ' - (x₀ + q * ρ')))| ≤
        |f ρ - f ρ'| + (|f ρ - (x₀ + q * ρ)| + |f ρ' - (x₀ + q * ρ')|) :=
      (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
    have h6 := mul_le_mul_of_nonneg_left h1 hq.le
    nlinarith only [h2, h3, h4, h5, h6]
  have hμ2 : 0 < μ - 2 * ε₁ := by linarith only [hε₁1, hμpos]
  have hinj : Set.InjOn f (profileRoots k : Set ℝ) := by
    intro ρ hρ ρ' hρ' heq
    by_contra hne
    have h1 := hfsep ρ ρ' hρ hρ' hne
    rw [heq, sub_self, abs_zero] at h1
    have h2 : 0 < q * (μ - 2 * ε₁) := by positivity
    linarith only [h1, h2]
  -- these are all the zeros of the window
  set Z := realZeroFinset t (x₀ - ε₀) (x₀ + ε₀) with hZ
  have himg : (profileRoots k).image f ⊆ Z := by
    intro w hw
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
    exact hfmem ρ hρ
  have hcardZ : Z.card ≤ k := by
    have h1 : Z.card ≤ realZeroCount t (x₀ - ε₀) (x₀ + ε₀) := by
      rw [realZeroCount, Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun w hw =>
        one_le_zeroMult_riemannHeat htpos.le ((mem_realZeroFinset htpos.le).mp hw).2
    rwa [hcnt] at h1
  have hcardimg : ((profileRoots k).image f).card = k := by
    rw [Finset.card_image_of_injOn hinj, card_profileRoots]
  have heq : (profileRoots k).image f = Z :=
    Finset.eq_of_subset_of_card_le himg (by rw [hcardimg]; exact hcardZ)
  have hyZ (w : ℝ) (hw : |w - x₀| ≤ ε₀) (h0' : riemannHeat t (w : ℂ) = 0) : w ∈ Z := by
    refine (mem_realZeroFinset htpos.le).mpr ⟨?_, h0'⟩
    have := abs_le.mp hw
    constructor <;> linarith only [this.1, this.2]
  have hy1 := hyZ y hyr hy0
  have hy2 := hyZ y' hy'r hy'0
  rw [← heq] at hy1 hy2
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hy1
  obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_image.mp hy2
  have hne : ρ ≠ ρ' := by
    rintro rfl
    exact lt_irrefl _ hyy'
  have hgap := hfsep ρ ρ' hρ hρ' hne
  rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hyy')] at hgap
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ q * (μ - 2 * ε₁)) hgap 2
  refine le_trans ?_ hsq
  rw [mul_pow, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg q)
  have h4 : 4 * μ * ε₁ ≤ ε := by
    have h5 : ε₁ * (8 * μ + 1) ≤ ε := (le_div_iff₀ (by positivity)).mp hε₁2
    nlinarith only [h5, hε₁pos, hμpos]
  rw [← hμsq]
  nlinarith only [h4, sq_nonneg ε₁]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
