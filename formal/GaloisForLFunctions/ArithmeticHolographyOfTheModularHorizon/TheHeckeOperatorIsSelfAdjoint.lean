import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheHeckeCosetsOfDeterminantP
import GaloisForLFunctions.RHTower.Gamma0MaassHeckeOperator
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainMeasure
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume

/-!
# The Hecke operator is self-adjoint

For a prime `p` the Hecke operator `T_p f(z) = Σ_k f(α_k z)` (`RHTower.Gamma0MaassHecke.heckeH`) is symmetric for the
pairing `⟨f, g⟩ = ∫_𝒟 f ḡ` of seeds (`integral_heckeH_mul_conj`).

**Proof.** Substitute `z = α_i^* w` in `∫_𝒟 f(α_i z) ḡ(z)` (the action of `GL₂⁺(ℝ)` preserves `dx dy/y²`, and
`α_i α_i^* = p`) and unfold `ℍ = ⋃_γ γ𝒟` over `PSL₂(ℤ)`:

  `⟨T_p f, g⟩ = ∫_𝒟 f(w) Σ_{i, γ} (1_𝒟 ḡ)(α_i^* γ w) dw`.

The Hecke bijection `(i, γ) ↦ (γ', k)`, `α_i^* γ = γ' α_k` (`HeckeCoset.heckeEquiv`), descends to `PSL₂(ℤ)`
(`pslEquiv`), so the inner sum is `Σ_k Σ_{γ'} (1_𝒟 ḡ)(γ' α_k w)`. Off the null set of points with a translate on the
boundary of `𝒟` exactly one `γ'` puts `α_k w` into `𝒟` (`tsum_indicator_fd`), and the sum is `Σ_k ḡ(α_k w)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HeckeAdjoint

open HeckeCoset GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower.Gamma0MaassHecke (alphaQ alphaMat heckeH)

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### The Hecke matrices in `GL₂(ℝ)` -/

/-- `α_k` in `GL₂(ℝ)`. -/
def alphaR (k : Option (ZMod p)) : GL (Fin 2) ℝ := (alphaQ p k).map (algebraMap ℚ ℝ)

/-- `α_i^*` in `GL₂(ℝ)`. -/
def astarR (i : Option (ZMod p)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Astar p i).map (Int.castRingHom ℝ)) (by
    rw [show ((Astar p i).map (Int.castRingHom ℝ)).det = Int.castRingHom ℝ (Astar p i).det from
      ((Int.castRingHom ℝ).map_det (Astar p i)).symm, det_Astar]
    simp [hp.out.ne_zero])

theorem alphaR_val (k : Option (ZMod p)) :
    ((alphaR p k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (A p k).map (Int.castRingHom ℝ) := by
  ext i j
  rw [alphaR, Matrix.GeneralLinearGroup.map_apply]
  cases k <;> fin_cases i <;> fin_cases j <;>
    simp [alphaQ, alphaMat, A, Matrix.GeneralLinearGroup.mkOfDetNeZero, -ZMod.natCast_val]

theorem astarR_val (i : Option (ZMod p)) :
    ((astarR p i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Astar p i).map (Int.castRingHom ℝ) := rfl

omit hp in
theorem mapGL_val (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) := by
  ext i j; simp [Matrix.SpecialLinearGroup.mapGL]

theorem heckeH_eq_sum (f : ℍ → ℂ) (z : ℍ) : heckeH p f z = ∑ k : Option (ZMod p), f (alphaR p k • z) := rfl

omit hp in
theorem A_mul_Astar (i : Option (ZMod p)) : A p i * Astar p i = !![(p : ℤ), 0; 0, (p : ℤ)] := by
  cases i <;> (ext a b; fin_cases a <;> fin_cases b <;>
    simp [A, Astar, Matrix.mul_apply, Fin.sum_univ_two, -ZMod.natCast_val])

/-- `α_i (α_i^* w) = w`: the product `α_i α_i^* = p` is a scalar. -/
theorem alphaR_smul_astarR (i : Option (ZMod p)) (w : ℍ) : alphaR p i • (astarR p i • w) = w := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hval : ((alphaR p i * astarR p i : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; 0, (p : ℝ)] := by
    rw [Units.val_mul, alphaR_val, astarR_val, ← Matrix.map_mul, A_mul_Astar]
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det (alphaR p i * astarR p i) : ℝˣ) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hval, Matrix.det_fin_two_of, mul_zero, sub_zero]; positivity
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [smul_smul]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hval]
  simp
  field_simp

/-- **The point identity** `α_i^* γ w = γ' α_k w` for `(γ', k) = heckeEquiv (i, γ)`. -/
theorem astarR_smul_SL (i : Option (ZMod p)) (γ : SL(2, ℤ)) (w : ℍ) :
    astarR p i • (γ • w) = (heckeEquiv p (i, γ)).1 • (alphaR p (heckeEquiv p (i, γ)).2 • w) := by
  show astarR p i • (Matrix.SpecialLinearGroup.mapGL ℝ γ • w) =
    Matrix.SpecialLinearGroup.mapGL ℝ (heckeEquiv p (i, γ)).1 • (alphaR p (heckeEquiv p (i, γ)).2 • w)
  rw [smul_smul, smul_smul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, astarR_val, mapGL_val, mapGL_val, alphaR_val, ← Matrix.map_mul,
    ← Matrix.map_mul]
  exact congrArg (fun M => M.map (Int.castRingHom ℝ)) (heckeEquiv_spec p (i, γ))

/-! ### The bijection on `PSL₂(ℤ)` -/

omit hp in
theorem mem_kernel {h : SL(2, ℤ)} (hh : h ∈ modularActionKernel) : h = 1 ∨ h = -1 := by
  set z₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩
  have hz₀ : z₀ ∈ ModularGroup.fdo := by
    constructor
    · show 1 < Complex.normSq (⟨0, 2⟩ : ℂ); rw [Complex.normSq_mk]; norm_num
    · show |(⟨0, 2⟩ : ℂ).re| < 1 / 2; norm_num
  have hfix : h • z₀ = z₀ := by
    have := congrArg (fun φ : Equiv.Perm ℍ => φ z₀) (MonoidHom.mem_ker.1 hh)
    simpa [MulAction.toPermHom_apply] using this
  exact ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hz₀ (by rw [hfix]; exact ModularGroup.fdo_subset_fd hz₀)

omit hp in
theorem out_mk (Q : SL(2, ℤ)) : (QuotientGroup.mk Q : PSL2Z).out = Q ∨ (QuotientGroup.mk Q : PSL2Z).out = -Q := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul modularActionKernel Q
  rcases mem_kernel h.2 with h1 | h1
  · left; rw [hh, h1, mul_one]
  · right; rw [hh, h1, mul_neg, mul_one]

omit hp in
theorem mk_neg (Q : SL(2, ℤ)) : (QuotientGroup.mk (-Q) : PSL2Z) = QuotientGroup.mk Q :=
  (PSL2Z_mk_eq_of_eq_or_eq_neg (Or.inr (by rw [mul_neg, inv_mul_cancel]))).symm

theorem heckeEquiv_symm_neg (γ' : SL(2, ℤ)) (k : Option (ZMod p)) :
    (heckeEquiv p).symm (-γ', k) = (((heckeEquiv p).symm (γ', k)).1, -((heckeEquiv p).symm (γ', k)).2) := by
  rw [Equiv.symm_apply_eq]
  have h := heckeEquiv_neg p ((heckeEquiv p).symm (γ', k)).1 ((heckeEquiv p).symm (γ', k)).2
  rw [Prod.mk.eta, Equiv.apply_symm_apply] at h
  exact h.symm

/-- **The Hecke bijection on `PSL₂(ℤ)`.** -/
def pslEquiv : Option (ZMod p) × PSL2Z ≃ PSL2Z × Option (ZMod p) where
  toFun q := (QuotientGroup.mk (heckeEquiv p (q.1, q.2.out)).1, (heckeEquiv p (q.1, q.2.out)).2)
  invFun q := (((heckeEquiv p).symm (q.1.out, q.2)).1, QuotientGroup.mk ((heckeEquiv p).symm (q.1.out, q.2)).2)
  left_inv q := by
    obtain ⟨i, γ⟩ := q
    simp only
    set Q := (heckeEquiv p (i, γ.out)).1
    set k := (heckeEquiv p (i, γ.out)).2
    have hQk : (Q, k) = heckeEquiv p (i, γ.out) := rfl
    rcases out_mk Q with h | h
    · rw [h, hQk, Equiv.symm_apply_apply]
      simp
    · rw [h, heckeEquiv_symm_neg, hQk, Equiv.symm_apply_apply]
      simp [mk_neg]
  right_inv q := by
    obtain ⟨γ', k⟩ := q
    simp only
    set i := ((heckeEquiv p).symm (γ'.out, k)).1
    set γ := ((heckeEquiv p).symm (γ'.out, k)).2
    have hiγ : heckeEquiv p (i, γ) = (γ'.out, k) := by
      rw [show (i, γ) = (heckeEquiv p).symm (γ'.out, k) from rfl, Equiv.apply_symm_apply]
    rcases out_mk γ with h | h
    · rw [h, hiγ]; simp
    · rw [h, heckeEquiv_neg, hiγ]; simp [mk_neg]

theorem PSL2Z_smul_eq_out (γ : PSL2Z) (w : ℍ) : γ • w = γ.out • w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact PSL2Z_mk_smul _ _

/-- The point identity on `PSL₂(ℤ)`. -/
theorem astarR_smul_PSL (i : Option (ZMod p)) (γ : PSL2Z) (w : ℍ) :
    astarR p i • (γ • w) = (pslEquiv p (i, γ)).1 • (alphaR p (pslEquiv p (i, γ)).2 • w) := by
  rw [PSL2Z_smul_eq_out γ, astarR_smul_SL]
  show _ = (QuotientGroup.mk (heckeEquiv p (i, γ.out)).1 : PSL2Z) • _
  rw [PSL2Z_mk_smul]
  rfl

/-! ### One translate in the fundamental domain -/

/-- Points with some translate on the boundary of `𝒟`. -/
def badSet : Set ℍ := ⋃ γ : PSL2Z, (fun x => γ • x) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo)

omit hp in
theorem volume_badSet : (volume : Measure ℍ) badSet = 0 := by
  refine measure_iUnion_null fun γ => ?_
  rw [(measurePreserving_smul γ (volume : Measure ℍ)).measure_preimage
    (ModularGroup.isClosed_fd.measurableSet.diff
      (ModularGroup.isOpen_fdo.measurableSet)).nullMeasurableSet]
  exact volume_fd_diff_fdo

omit hp in
/-- Off the bad set at most one translate of `x` lies in `𝒟`. -/
theorem eq_of_smul_mem_fd {x : ℍ} (hx : x ∉ badSet) {γ₁ γ₂ : PSL2Z} (h₁ : γ₁ • x ∈ ModularGroup.fd)
    (h₂ : γ₂ • x ∈ ModularGroup.fd) : γ₂ = γ₁ := by
  have hin : γ₁ • x ∈ ModularGroup.fdo := by
    by_contra hno
    exact hx (mem_iUnion.2 ⟨γ₁, h₁, hno⟩)
  set δ := γ₂ * γ₁⁻¹
  have hδ : δ • (γ₁ • x) = γ₂ • x := by rw [smul_smul, inv_mul_cancel_right]
  have hδ' : δ.out • (γ₁ • x) ∈ ModularGroup.fd := by
    rw [← PSL2Z_smul_eq_out, hδ]; exact h₂
  have h1 : δ = 1 := by
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hin hδ' with h | h
    · rw [← QuotientGroup.out_eq' δ, h]; rfl
    · rw [← QuotientGroup.out_eq' δ, h, mk_neg]; rfl
  calc γ₂ = δ * γ₁ := by rw [inv_mul_cancel_right]
    _ = γ₁ := by rw [h1, one_mul]

omit hp in
theorem psl_invariant {h : ℍ → ℂ} (hh : ∀ (γ : SL(2, ℤ)) (z : ℍ), h (γ • z) = h z) (γ : PSL2Z) (z : ℍ) :
    h (γ • z) = h z := by
  rw [PSL2Z_smul_eq_out, hh]

omit hp in
/-- **Exactly one translate.** Off the bad set, `Σ_γ (1_𝒟 h)(γ x) = h(x)` for an invariant `h`. -/
theorem tsum_indicator_fd {h : ℍ → ℂ} (hh : ∀ (γ : PSL2Z) (x : ℍ), h (γ • x) = h x) {x : ℍ} (hx : x ∉ badSet) :
    ∑' γ : PSL2Z, ModularGroup.fd.indicator h (γ • x) = h x := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd x
  set γ₀ : PSL2Z := QuotientGroup.mk g
  have hγ₀ : γ₀ • x ∈ ModularGroup.fd := by rw [PSL2Z_mk_smul]; exact hg
  rw [tsum_eq_single γ₀ fun γ hγ => indicator_of_notMem (fun hm => hγ (eq_of_smul_mem_fd hx hγ₀ hm)) _,
    indicator_of_mem hγ₀, hh]

/-! ### The orbit sum of the adjoint cosets -/

/-- `1_𝒟 ḡ`. -/
def conjInd (g : ℍ → ℂ) : ℍ → ℂ := ModularGroup.fd.indicator fun z => conj (g z)

/-- The term `(1_𝒟 ḡ)(γ' α_k w)` of the orbit sum. -/
def orbitTerm (g : ℍ → ℂ) (w : ℍ) (q : PSL2Z × Option (ZMod p)) : ℂ := conjInd g (q.1 • (alphaR p q.2 • w))

theorem summable_orbitTerm (g : ℍ → ℂ) {w : ℍ} (hw : ∀ j : Option (ZMod p), alphaR p j • w ∉ badSet) :
    Summable (orbitTerm p g w) := by
  refine summable_of_hasFiniteSupport (Set.Finite.subset ((Set.finite_iUnion fun j : Option (ZMod p) =>
    (show {γ : PSL2Z | γ • (alphaR p j • w) ∈ ModularGroup.fd}.Subsingleton from
      fun γ₁ h₁ γ₂ h₂ => (eq_of_smul_mem_fd (hw j) h₁ h₂).symm).finite).prod Set.finite_univ) ?_)
  rintro ⟨γ', j⟩ hq
  refine ⟨mem_iUnion.2 ⟨j, show γ' • (alphaR p j • w) ∈ ModularGroup.fd from ?_⟩, trivial⟩
  by_contra hno
  exact hq (show conjInd g (γ' • (alphaR p j • w)) = 0 from indicator_of_notMem hno _)

/-- **The adjoint coset sum.** For `w` whose Hecke images avoid the bad set,
`Σ_γ Σ_i (1_𝒟 ḡ)(α_i^* γ w) = Σ_k ḡ(α_k w)`: by the Hecke bijection the left side is the sum of
`(1_𝒟 ḡ)(γ' α_k w)` over `(γ', k)`, and for each `k` exactly one `γ'` contributes. -/
theorem tsum_sum_astar {g : ℍ → ℂ} (hg : ∀ (γ : SL(2, ℤ)) (z : ℍ), g (γ • z) = g z) {w : ℍ}
    (hw : ∀ j : Option (ZMod p), alphaR p j • w ∉ badSet) :
    ∑' γ : PSL2Z, ∑ k : Option (ZMod p), conjInd g (astarR p k • (γ • w)) =
      ∑ j : Option (ZMod p), conj (g (alphaR p j • w)) := by
  have hΨ := summable_orbitTerm p g hw
  have hΦ : Summable (orbitTerm p g w ∘ pslEquiv p) := (pslEquiv p).summable_iff.2 hΨ
  have hs : Summable (orbitTerm p g w ∘ Equiv.prodComm _ _) := (Equiv.prodComm _ _).summable_iff.2 hΨ
  have hΦeq : ∀ k γ, conjInd g (astarR p k • (γ • w)) = (orbitTerm p g w ∘ pslEquiv p) (k, γ) := fun k γ =>
    congrArg (conjInd g) (astarR_smul_PSL p k γ w)
  have hinv : ∀ (γ : PSL2Z) (x : ℍ), conj (g (γ • x)) = conj (g x) := fun γ x => by
    rw [psl_invariant hg]
  calc ∑' γ : PSL2Z, ∑ k : Option (ZMod p), conjInd g (astarR p k • (γ • w))
        = ∑ k : Option (ZMod p), ∑' γ : PSL2Z, (orbitTerm p g w ∘ pslEquiv p) (k, γ) := by
          simp_rw [hΦeq]
          exact Summable.tsum_finsetSum fun k _ => hΦ.prod_factor k
      _ = ∑' q, (orbitTerm p g w ∘ pslEquiv p) q := by
          rw [hΦ.tsum_prod' (fun k => hΦ.prod_factor k), tsum_fintype]
      _ = ∑' q, orbitTerm p g w q := (pslEquiv p).tsum_eq _
      _ = ∑' q, (orbitTerm p g w ∘ Equiv.prodComm _ _) q := ((Equiv.prodComm _ _).tsum_eq _).symm
      _ = ∑ j : Option (ZMod p), ∑' γ' : PSL2Z, (orbitTerm p g w ∘ Equiv.prodComm _ _) (j, γ') := by
          rw [hs.tsum_prod' (fun j => hs.prod_factor j), tsum_fintype]
      _ = ∑ j : Option (ZMod p), conj (g (alphaR p j • w)) :=
          Finset.sum_congr rfl fun j _ => tsum_indicator_fd (h := fun z => conj (g z)) hinv (hw j)

/-! ### Unfolding and self-adjointness -/

omit hp in
/-- **Unfolding.** `∫_ℍ F = ∫_𝒟 Σ_γ F(γ w)` for integrable `F`. -/
theorem integral_eq_setIntegral_tsum {F : ℍ → ℂ} (hF : Integrable F) :
    ∫ w, F w = ∫ w in ModularGroup.fd, ∑' γ : PSL2Z, F (γ • w) := by
  rw [isFundamentalDomain_fd.integral_eq_tsum'' F hF]
  symm
  apply integral_tsum
  · intro γ
    exact (hF.aestronglyMeasurable.comp_measurePreserving (measurePreserving_smul γ volume)).restrict
  · rw [← isFundamentalDomain_fd.lintegral_eq_tsum'' (fun x => ‖F x‖ₑ)]
    exact hF.2.ne

/-- **The Hecke operator is self-adjoint**: for bounded measurable `SL₂(ℤ)`-invariant `f`, `g`,
`∫_𝒟 (T_p f) ḡ = ∫_𝒟 f (T_p g)‾`. -/
theorem integral_heckeH_mul_conj {f g : ℍ → ℂ} (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∃ C, ∀ z, ‖f z‖ ≤ C) (hgb : ∃ C, ∀ z, ‖g z‖ ≤ C)
    (hf : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = f z) (hg : ∀ (γ : SL(2, ℤ)) (z : ℍ), g (γ • z) = g z) :
    ∫ z in ModularGroup.fd, heckeH p f z * conj (g z) = ∫ z in ModularGroup.fd, f z * conj (heckeH p g z) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hfdm : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  haveI : IsFiniteMeasure ((volume : Measure ℍ).restrict ModularGroup.fd) :=
    isFiniteMeasure_restrict.2 volume_fd_lt_top.ne
  have hgc : Measurable fun z => conj (g z) := Complex.continuous_conj.measurable.comp hgm
  have hpt : ∀ k w, ModularGroup.fd.indicator (fun z => f (alphaR p k • z) * conj (g z)) (astarR p k • w) =
      f w * conjInd g (astarR p k • w) := fun k w => by
    by_cases hw : astarR p k • w ∈ ModularGroup.fd
    · rw [conjInd, indicator_of_mem hw, indicator_of_mem hw, alphaR_smul_astarR]
    · rw [conjInd, indicator_of_notMem hw, indicator_of_notMem hw, mul_zero]
  have hon : ∀ k, IntegrableOn (fun z => f (alphaR p k • z) * conj (g z)) ModularGroup.fd := fun k =>
    Integrable.of_bound ((hfm.comp (measurable_const_smul _)).mul hgc).aestronglyMeasurable (Cf * Cg)
      (ae_of_all _ fun z => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hCf _) (hCg _) (norm_nonneg _) ((norm_nonneg _).trans (hCf z)))
  have hmp : ∀ k, MeasurePreserving (fun w : ℍ => astarR p k • w) volume volume := fun k =>
    measurePreserving_smul _ volume
  have hint : ∀ k, Integrable (fun w => f w * conjInd g (astarR p k • w)) := fun k => by
    have h := ((hmp k).integrable_comp_emb (measurableEmbedding_const_smul _)).2
      ((integrable_indicator_iff hfdm).2 (hon k))
    exact h.congr (ae_of_all _ fun w => hpt k w)
  -- each Hecke term, moved to `ℍ` by `z = α_k^* w`
  have hterm : ∀ k, ∫ z in ModularGroup.fd, f (alphaR p k • z) * conj (g z) =
      ∫ w, f w * conjInd g (astarR p k • w) := fun k => by
    rw [← integral_indicator hfdm, ← (hmp k).integral_comp (measurableEmbedding_const_smul _)]
    exact integral_congr_ae (ae_of_all _ fun w => hpt k w)
  -- the good points
  have hgood : ∀ᵐ w ∂(volume : Measure ℍ), ∀ j : Option (ZMod p), alphaR p j • w ∉ badSet :=
    ae_all_iff.2 fun j => measure_eq_zero_iff_ae_notMem.1
      ((measurePreserving_smul (alphaR p j) volume).quasiMeasurePreserving.preimage_null volume_badSet)
  have hΘ : Integrable (fun w => f w * ∑ k : Option (ZMod p), conjInd g (astarR p k • w)) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun k _ => hint k
  calc ∫ z in ModularGroup.fd, heckeH p f z * conj (g z)
        = ∑ k : Option (ZMod p), ∫ z in ModularGroup.fd, f (alphaR p k • z) * conj (g z) := by
          simp_rw [heckeH_eq_sum, Finset.sum_mul]
          exact integral_finsetSum _ fun k _ => hon k
      _ = ∫ w, f w * ∑ k : Option (ZMod p), conjInd g (astarR p k • w) := by
          simp_rw [hterm, Finset.mul_sum]
          exact (integral_finsetSum _ fun k _ => hint k).symm
      _ = ∫ w in ModularGroup.fd, f w * ∑' γ : PSL2Z, ∑ k : Option (ZMod p), conjInd g (astarR p k • (γ • w)) := by
          rw [integral_eq_setIntegral_tsum hΘ]
          simp_rw [psl_invariant hf, tsum_mul_left]
      _ = ∫ z in ModularGroup.fd, f z * conj (heckeH p g z) := by
          refine integral_congr_ae (ae_restrict_of_ae (hgood.mono fun w hw => ?_))
          simp only
          rw [tsum_sum_astar p hg hw, heckeH_eq_sum, map_sum]

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HeckeAdjoint
