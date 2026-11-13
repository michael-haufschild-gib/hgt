import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionGroup
import GaloisForLFunctions.HTGeometry.LatticeMinkowskiBound

/-!
# `Γ(N)` is cocompact

For `h ∈ SL(2, ℝ)` the lattice `h·ι(O) ⊂ M₂(ℝ) ≅ ℝ⁴` has covolume `24` (`det_latBasis`), so
Minkowski's theorem gives `x ∈ O ∖ 0` with all entries of `h·ι(x)` at most `3` (`exists_short`).
Then `1 ≤ |nrd x| ≤ 18` (anisotropy and `|det| ≤ 18`).  Elements with the same norm `n` and the
same coordinates mod `|n|N` differ by an element of `Γ(N)`: `x = γ r` with `γ = x r̄ / n`
(`exists_congGroup_mul_of_quatKey_eq`).  With finitely many representatives `r`, the matrix
`h·γ = h·ι(x)·ι(r)⁻¹` has bounded entries, i.e. `γ⁻¹·z` lies in a fixed ball around `i`, for
`z = h⁻¹·i` (`exists_compact_congGroup`).

Main result: `isCocompactFree_congGroup` — for `N ≥ 3`, `Γ(N)` is a cocompact Fuchsian group acting
freely on `ℍ`.
-/

open Matrix UpperHalfPlane MeasureTheory
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The lattice `h·ι(O)` -/

/-- `M ↦ (m₀₀, m₀₁, m₁₀, m₁₁)`. -/
def flat (M : Matrix (Fin 2) (Fin 2) ℝ) : Fin 4 → ℝ := ![M 0 0, M 0 1, M 1 0, M 1 1]

/-- `v ↦ flat (h·quatMatR v)`; the lattice `h·ι(O)` is the image of `ℤ⁴`. -/
def latMap (h : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := flat (h * quatMatR v)
  map_add' v w := by
    funext k
    fin_cases k <;> simp [flat, quatMatR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail] <;> ring
  map_smul' c v := by
    funext k
    fin_cases k <;> simp [flat, quatMatR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail] <;> ring

theorem eq_zero_of_flat_eq_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (h : flat M = 0) : M = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [flat] using congrFun h 0
  · simpa [flat] using congrFun h 1
  · simpa [flat] using congrFun h 2
  · simpa [flat] using congrFun h 3

theorem latMap_injective (h : SL(2, ℝ)) :
    Function.Injective (latMap (h : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hM : (h : Matrix (Fin 2) (Fin 2) ℝ) * quatMatR v = 0 := eq_zero_of_flat_eq_zero hv
  have e : ((h⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * (h : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hQ : quatMatR v = 0 := by
    calc quatMatR v = (((h⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
          (h : Matrix (Fin 2) (Fin 2) ℝ)) * quatMatR v := by rw [e, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, hM, Matrix.mul_zero]
  have hv' := quatCoeff_quatMatR v
  rw [hQ] at hv'
  rw [← hv']
  funext k
  fin_cases k <;> simp [quatCoeff]

/-- The basis `h·ι(e_k)` of the lattice `h·ι(O)`. -/
def latBasis (h : SL(2, ℝ)) : Module.Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
  (Pi.basisFun ℝ (Fin 4)).map (LinearEquiv.ofInjectiveEndo _ (latMap_injective h))

theorem latBasis_apply (h : SL(2, ℝ)) (i : Fin 4) :
    latBasis h i = latMap (h : Matrix (Fin 2) (Fin 2) ℝ) (Pi.basisFun ℝ (Fin 4) i) := by
  rw [latBasis, Module.Basis.map_apply, LinearEquiv.coe_ofInjectiveEndo]

/-- **The covolume of `h·ι(O)` is `24`.** -/
theorem det_latBasis (h : SL(2, ℝ)) : (Matrix.of (latBasis h)).det = 24 := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe h
    rwa [Matrix.det_fin_two] at this
  have hs := sqrt_two_mul_self
  have hM : Matrix.of (latBasis h) =
      !![h 0 0, h 0 1, h 1 0, h 1 1;
        h 0 0 * √2, -(h 0 1 * √2), h 1 0 * √2, -(h 1 1 * √2);
        h 0 1, 3 * h 0 0, h 1 1, 3 * h 1 0;
        -(h 0 1 * √2), 3 * (h 0 0 * √2), -(h 1 1 * √2), 3 * (h 1 0 * √2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [latBasis_apply, latMap, flat, quatMatR, Matrix.mul_apply, Fin.sum_univ_two,
        Pi.basisFun_apply, Pi.single_apply, Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [hM, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove, Matrix.submatrix,
    Matrix.vecHead, Matrix.vecTail]
  have key : (h 0 0 * h 1 1 - h 0 1 * h 1 0) ^ 2 = 1 := by rw [hdet]; ring
  linear_combination (exp := 1) (12 * (h 0 0 * h 1 1 - h 0 1 * h 1 0) ^ 2) * hs + 24 * key

/-- **Minkowski.**  Some `x ∈ O ∖ 0` has all entries of `h·ι(x)` at most `3`. -/
theorem exists_short (h : SL(2, ℝ)) : ∃ c : Fin 4 → ℤ, c ≠ 0 ∧
    ∀ i j, |((h : Matrix (Fin 2) (Fin 2) ℝ) * quatMat c) i j| ≤ 3 := by
  set b := latBasis h
  haveI : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    refine Function.Surjective.countable (f := fun c : Fin 4 → ℤ =>
      (⟨∑ i, c i • b i, Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩ :
        (Submodule.span ℤ (Set.range b)).toAddSubgroup)) ?_
    rintro ⟨v, hv⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
    exact ⟨c, Subtype.ext hc⟩
  have hfund := ZSpan.isAddFundamentalDomain' b volume
  have hvol : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal 24 := by
    rw [ZSpan.volume_fundamentalDomain, det_latBasis]; norm_num
  have hball : volume (Metric.closedBall (0 : Fin 4 → ℝ) 3) = ENNReal.ofReal ((2 * 3) ^ 4) := by
    rw [Real.volume_pi_closedBall _ (by norm_num)]; simp
  obtain ⟨v, hvL, hv0, hvn⟩ := exists_ne_zero_norm_le_of_covolume (μ := volume) hfund (r := 3)
    (by
      rw [hvol, hball, Module.finrank_fin_fun, ← ENNReal.ofReal_pow (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hvL
  have hvc : v = latMap (h : Matrix (Fin 2) (Fin 2) ℝ) (fun k => (c k : ℝ)) := by
    rw [← hc]
    have : (fun k => (c k : ℝ)) = ∑ i, (c i : ℝ) • Pi.basisFun ℝ (Fin 4) i := by
      funext k
      simp [Pi.basisFun_apply, Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [latBasis_apply, map_smul, Int.cast_smul_eq_zsmul]
  refine ⟨c, ?_, fun i j => ?_⟩
  · rintro rfl
    apply hv0
    rw [hvc]
    have : (fun k => ((0 : Fin 4 → ℤ) k : ℝ)) = 0 := by funext k; simp
    rw [this, map_zero]
  · have hk : ∀ k, |v k| ≤ 3 := fun k => by
      have := (norm_le_pi_norm v k).trans hvn
      rwa [Real.norm_eq_abs] at this
    rw [hvc] at hk
    fin_cases i <;> fin_cases j
    · exact hk 0
    · exact hk 1
    · exact hk 2
    · exact hk 3

/-! ### Elements with equal residue data -/

/-- The norm and the coordinates mod `|nrd x|·N`. -/
def quatKey (N : ℕ) (x : Fin 4 → ℤ) : ℤ × (Fin 4 → ℤ) :=
  (nrd x, fun k => x k % (((nrd x).natAbs * N : ℕ) : ℤ))

theorem finite_quatKey {N : ℕ} (hN : 0 < N) :
    (quatKey N '' {x | nrd x ≠ 0 ∧ |nrd x| ≤ 18}).Finite := by
  refine ((Set.finite_Icc (-18 : ℤ) 18).prod
    (Set.Finite.pi fun _ => Set.finite_Icc (0 : ℤ) (18 * N))).subset ?_
  rintro _ ⟨x, ⟨hx0, hx18⟩, rfl⟩
  have hm : (0 : ℤ) < (((nrd x).natAbs * N : ℕ) : ℤ) := by
    have : 0 < (nrd x).natAbs := Int.natAbs_pos.mpr hx0
    positivity
  have hm18 : (((nrd x).natAbs * N : ℕ) : ℤ) ≤ 18 * N := by
    have : ((nrd x).natAbs : ℤ) ≤ 18 := by rw [Int.natCast_natAbs]; exact hx18
    push_cast
    nlinarith
  refine ⟨abs_le.mp hx18, fun k _ => ⟨Int.emod_nonneg _ hm.ne', ?_⟩⟩
  exact ((Int.emod_lt_of_pos _ hm).le.trans (by linarith)).trans hm18

/-- **Equal residue data differ by `Γ(N)`.**  If `nrd x = nrd r = n ≠ 0` and `x ≡ r mod |n|N`,
then `x = γ r` with `γ = x r̄ / n ∈ Γ(N)`. -/
theorem exists_congGroup_mul_of_quatKey_eq {N : ℕ} {x r : Fin 4 → ℤ} (hr : nrd r ≠ 0)
    (hk : quatKey N x = quatKey N r) :
    ∃ y, nrd y = 1 ∧ IsCong N y ∧ quatMat y * quatMat r = quatMat x := by
  have hn : nrd x = nrd r := congrArg Prod.fst hk
  set n := nrd r with hndef
  set m : ℤ := ((n.natAbs * N : ℕ) : ℤ) with hmdef
  have hres : ∀ k, x k % m = r k % m := by
    intro k
    have := congrFun (congrArg Prod.snd hk) k
    simpa only [quatKey, hn] using this
  have hdvd : ∀ k, m ∣ x k - r k := fun k => Int.ModEq.dvd (hres k).symm
  choose w hw using hdvd
  have hxw : x = r + m • w := funext fun k => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hw k]
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, m = n * (ε * N) := by
    rcases lt_or_gt_of_ne hr with h | h
    · refine ⟨-1, ?_⟩
      rw [hmdef]; push_cast; rw [Int.ofNat_natAbs_of_nonpos h.le]; ring
    · refine ⟨1, ?_⟩
      rw [hmdef]; push_cast; rw [Int.natAbs_of_nonneg h.le]; ring
  set W := quatMul w (quatConj r)
  set y := quatOne + (N : ℤ) • (ε • W) with hy
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hr
  have hadj : quatMat r * quatMat (quatConj r) = (n : ℝ) • 1 := by
    rw [← adjugate_quatMat, Matrix.mul_adjugate, det_quatMat]
  have hadj' : quatMat (quatConj r) * quatMat r = (n : ℝ) • 1 := by
    rw [← adjugate_quatMat, Matrix.adjugate_mul, det_quatMat]
  have hY : (n : ℝ) • quatMat y = quatMat x * quatMat (quatConj r) := by
    rw [hxw, quatMat_add, Matrix.add_mul, hadj, quatMat_smul, Matrix.smul_mul, quatMat_mul, hy,
      quatMat_add, quatMat_one, quatMat_smul, quatMat_smul, smul_add, smul_smul, smul_smul, hε]
    push_cast
    ring_nf
  have hMat : quatMat y * quatMat r = quatMat x := by
    have h2 : (n : ℝ) • (quatMat y * quatMat r) = (n : ℝ) • quatMat x := by
      rw [← Matrix.smul_mul, hY, Matrix.mul_assoc, hadj', Matrix.mul_smul, Matrix.mul_one]
    exact smul_right_injective _ hnR h2
  refine ⟨y, ?_, ⟨ε • W, rfl⟩, hMat⟩
  have hd := congrArg Matrix.det hMat
  rw [det_mul, det_quatMat, det_quatMat, det_quatMat, hn] at hd
  have : ((nrd y : ℤ) : ℝ) = 1 := mul_right_cancel₀ hnR (by rw [hd, one_mul])
  exact_mod_cast this

/-! ### Cocompactness -/

theorem abs_mul_apply_le {A C : Matrix (Fin 2) (Fin 2) ℝ} {s t : ℝ} (hA : ∀ i j, |A i j| ≤ s)
    (hC : ∀ i j, |C i j| ≤ t) (i j : Fin 2) : |(A * C) i j| ≤ 2 * s * t := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hs : 0 ≤ s := (abs_nonneg _).trans (hA 0 0)
  have h1 : |A i 0 * C 0 j| ≤ s * t := by
    rw [abs_mul]; exact mul_le_mul (hA i 0) (hC 0 j) (abs_nonneg _) hs
  have h2 : |A i 1 * C 1 j| ≤ s * t := by
    rw [abs_mul]; exact mul_le_mul (hA i 1) (hC 1 j) (abs_nonneg _) hs
  calc |A i 0 * C 0 j + A i 1 * C 1 j| ≤ |A i 0 * C 0 j| + |A i 1 * C 1 j| := abs_add_le _ _
    _ ≤ 2 * s * t := by linarith

theorem abs_apply_le_sum (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    |M i j| ≤ ∑ i', ∑ j', |M i' j'| :=
  (Finset.single_le_sum (f := fun j' => |M i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i' => ∑ j', |M i' j'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))

/-- `(cosh ρ − 1)/2 ≥ (ρ − 1)/4`. -/
theorem cosh_sub_one_div_two_ge (ρ : ℝ) : (ρ - 1) / 4 ≤ (Real.cosh ρ - 1) / 2 := by
  have h1 := Real.add_one_le_exp ρ
  have h2 := Real.exp_pos (-ρ)
  rw [Real.cosh_eq]
  linarith

/-- **A compact set meets every orbit of `Γ(N)`.** -/
theorem exists_compact_congGroup {N : ℕ} (hN : 0 < N) :
    ∃ K : Set ℍ, IsCompact K ∧ ∀ z : ℍ, ∃ γ : congGroup N, (γ : SL(2, ℝ)) • z ∈ K := by
  set S := {x : Fin 4 → ℤ | nrd x ≠ 0 ∧ |nrd x| ≤ 18}
  have hT := finite_quatKey (N := N) hN
  have hrep : ∀ κ ∈ quatKey N '' S, ∃ r ∈ S, quatKey N r = κ :=
    fun κ ⟨r, hr, e⟩ => ⟨r, hr, e⟩
  choose! rep hrepS hrepK using hrep
  obtain ⟨B₀, hB₀⟩ := (hT.image fun κ => ∑ i, ∑ j, |((quatMat (rep κ))⁻¹) i j|).bddAbove
  set B := max B₀ 0
  have hB : ∀ κ ∈ quatKey N '' S, ∀ i j, |((quatMat (rep κ))⁻¹) i j| ≤ B := fun κ hκ i j =>
    ((abs_apply_le_sum _ i j).trans (hB₀ ⟨κ, hκ, rfl⟩)).trans (le_max_left _ _)
  set U := 36 * B ^ 2
  set ρ := 4 * U + 1
  refine ⟨Metric.closedBall I ρ, isCompact_closedBall _ _, fun z => ?_⟩
  set h := (toSL2R z)⁻¹
  obtain ⟨c, hc0, hc3⟩ := exists_short h
  have hcS : c ∈ S := by
    refine ⟨fun h0 => hc0 (eq_zero_of_nrd_eq_zero c h0), ?_⟩
    have hdet : ((h : Matrix (Fin 2) (Fin 2) ℝ) * quatMat c).det = nrd c := by
      rw [det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, det_quatMat]
    rw [Matrix.det_fin_two] at hdet
    have e1 := abs_le.mp (hc3 0 0)
    have e2 := abs_le.mp (hc3 0 1)
    have e3 := abs_le.mp (hc3 1 0)
    have e4 := abs_le.mp (hc3 1 1)
    have : |(nrd c : ℝ)| ≤ 18 := by
      rw [← hdet, abs_le]; constructor <;> nlinarith
    exact_mod_cast this
  set κ := quatKey N c
  have hκ : κ ∈ quatKey N '' S := ⟨c, hcS, rfl⟩
  set r := rep κ
  have hrS : r ∈ S := hrepS κ hκ
  obtain ⟨y, hy1, hyc, hyr⟩ :=
    exists_congGroup_mul_of_quatKey_eq (N := N) hrS.1 (hrepK κ hκ).symm
  -- `γ' = ι(y) ∈ Γ(N)` and `h γ' = h ι(c) ι(r)⁻¹`
  have hydet : (quatMat y).det = 1 := by rw [det_quatMat, hy1]; norm_num
  set γ' : SL(2, ℝ) := ⟨quatMat y, hydet⟩
  have hγ' : γ' ∈ congGroup N := ⟨y, hy1, hyc, rfl⟩
  have hrunit : IsUnit (quatMat r).det := by
    rw [det_quatMat]; exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hrS.1)
  have hyc' : quatMat y = quatMat c * (quatMat r)⁻¹ := by
    rw [← hyr, Matrix.mul_nonsing_inv_cancel_right _ _ hrunit]
  have hent : ∀ i j, |((h * γ' : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 2 * 3 * B := by
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_mul, show ((γ' : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      quatMat y from rfl, hyc', ← Matrix.mul_assoc]
    exact abs_mul_apply_le hc3 (hB κ hκ) i j
  refine ⟨(⟨γ', hγ'⟩ : congGroup N)⁻¹, ?_⟩
  have hz : (toSL2R z) • I = z := toSL2R_smul_I z
  have hact : ((⟨γ', hγ'⟩ : congGroup N)⁻¹ : congGroup N).1 • z = (h * γ')⁻¹ • I := by
    rw [mul_inv_rev, inv_inv, mul_smul, hz]
    rfl
  rw [Metric.mem_closedBall, dist_comm, hact,
    dist_le_iff_pairU_le (by positivity : (0 : ℝ) ≤ ρ)]
  have h4 := four_mul_pairU_I_smul_I_add_two (h * γ')⁻¹
  have hinv : ∀ i j, ((h * γ')⁻¹ : SL(2, ℝ)) i j ^ 2 ≤ (2 * 3 * B) ^ 2 := by
    intro i j
    have : |((h * γ')⁻¹ : SL(2, ℝ)) i j| ≤ 2 * 3 * B := by
      rw [show ((h * γ')⁻¹ : SL(2, ℝ)) i j =
        ((((h * γ')⁻¹ : SL(2, ℝ))) : Matrix (Fin 2) (Fin 2) ℝ) i j from rfl,
        Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
      fin_cases i <;> fin_cases j <;> simp [abs_neg, hent]
    exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  have hU : pairU I ((h * γ')⁻¹ • I) ≤ U := by
    have := hinv 0 0; have := hinv 0 1; have := hinv 1 0; have := hinv 1 1
    nlinarith
  exact hU.trans ((by linarith : U ≤ (ρ - 1) / 4).trans (cosh_sub_one_div_two_ge ρ))

/-- **`Γ(N)` is a cocompact Fuchsian group acting freely** (`N ≥ 3`). -/
theorem isCocompactFree_congGroup {N : ℕ} (hN : 3 ≤ N) : IsCocompactFree (congGroup N) :=
  ⟨finite_dist_congGroup N, exists_compact_congGroup (by omega),
    eq_one_of_smul_eq_congGroup hN⟩

/-- **A compact hyperbolic surface.**  `Γ(N)\ℍ` (`N ≥ 3`) carries the structure
`CompactQuotient`: a measurable fundamental domain inside a compact set. -/
theorem exists_compactQuotient_congGroup {N : ℕ} (hN : 3 ≤ N) :
    ∃ X : CompactQuotient, X.Γ = congGroup N := by
  have hΓ := isCocompactFree_congGroup hN
  obtain ⟨F, K, hK, hFK, hF, hfd⟩ := hΓ.exists_isFundamentalDomain
  exact ⟨⟨congGroup N, hΓ, F, K, hK, hFK, hF, hfd⟩, rfl⟩

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
