import GaloisForLFunctions.HTGeometry.ZariskiTangentDual
import GaloisForLFunctions.HTGeometry.HankelSingularHeight
import GaloisForLFunctions.HTGeometry.DeterminantalJacobi

/-!
# Tangent spaces of the Hankel secant varieties: `Sing(C_k) = C_{k+1}`

Let `V_r ⊆ K^N` be the zero set of `I_r` (maximal `(r+1)`-minors of the Hankel matrix), of
dimension `2r`.  For `p ∈ V_{s+1}`, `2(s+1) < N`:

* `finrank_zariskiTangent_hankel` — if some maximal `(s+1)`-minor is nonzero at `p` (`p ∉ V_s`), the
  Zariski tangent space has dimension exactly `2(s+1)`: `p` is a smooth point;
* `zariskiTangent_hankel_eq_top` — if `p ∈ V_s`, every direction is tangent: the tangent space is
  all of `K^N`, of dimension `N > 2(s+1)`: `p` is singular.

At a point of the leading chart (`δ(y) ≠ 0`) the bordered minors
`g_n = det [[H, x_{·+n−r}], [x_{r+·}, x_n]]` have `∂g_n/∂x_n = δ` and `∂g_n/∂x_m = 0` for `m > n`, so a
tangent vector is determined by its first `2r` coordinates; conversely every choice of those is
realized, by evaluating the chart `A_δ ≅ K[y]_δ` at `y + ε e_k` over the dual numbers.  A moved chart
reduces every point off `V_s` to this case, and the tangent spaces at `p` and at the moved point are
isomorphic.  On `V_s` every derivative of a maximal `(s+2)`-minor is a combination of
`(s+1)`-minors (Jacobi's formula), which vanish there.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial TrivSqZeroExt

noncomputable section

variable (K : Type) [Field K]

/-- Every `(s+1)`-minor of the Hankel matrix, in any rows and columns, lies in `I_s`. -/
theorem hankelMinor_mem_secantIdeal {N s : ℕ} (ρ γ : Fin (s + 1) → ℕ)
    (h : ∀ a b, ρ a + γ b < N) :
    Matrix.det (fun a b => (X ⟨ρ a + γ b, h a b⟩ : MvPolynomial (Fin N) K)) ∈
      RHTower.finiteHankelSecantIdeal K N s := by
  rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker]
  have hmem := RHTower.deningerGenericHankelIdeal_le_secantParameterization_ker K s
    (RHTower.deningerMatrixMinorDet_mem (s + 1) (RHTower.deningerGenericMomentHankel K) ρ γ)
  rw [RingHom.mem_ker] at hmem
  rw [← hmem, RHTower.finiteHankelSecantParameterization, RingHom.comp_apply]
  congr 1
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp [RHTower.deningerGenericMomentHankel]

theorem secantIdeal_succ_le (N s : ℕ) :
    RHTower.finiteHankelSecantIdeal K N (s + 1) ≤ RHTower.finiteHankelSecantIdeal K N s :=
  (secantIdeal_le_originIdeal K N s).trans (originIdeal_le_secantIdeal K N s)

/-- **On `V_s` the secant ideal `I_{s+1}` vanishes to second order.** -/
theorem secantIdeal_le_sqIdeal {N s : ℕ} (p : Fin N → K)
    (hp : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N s, eval p g = 0) :
    RHTower.finiteHankelSecantIdeal K N (s + 1) ≤ sqIdeal p := by
  rw [RHTower.finiteHankelSecantIdeal, Ideal.span_le]
  rintro _ ⟨c, hbound, hc, rfl⟩
  refine ⟨hp _ (secantIdeal_succ_le K N s (Ideal.subset_span ⟨c, hbound, hc, rfl⟩)), fun n => ?_⟩
  set M : Matrix (Fin (s + 1 + 1)) (Fin (s + 1 + 1)) (MvPolynomial (Fin N) K) :=
    fun i j => X (RHTower.finiteHankelIndex c hbound i j) with hM
  have hD := derivation_det_submatrix_mem_detIdeal (pderiv n) M id id
  have hle : detIdeal M (s + 1) ≤ RingHom.ker (eval p) := by
    refine detIdeal_le fun I' m' => RingHom.mem_ker.mpr (hp _ ?_)
    have := hankelMinor_mem_secantIdeal K (N := N) (s := s) (fun a => I' a) (fun b => c (m' b))
      (fun a b => by have := hbound (m' b); have := (I' a).isLt; omega)
    convert this using 2
    funext a b
    rfl
  have := RingHom.mem_ker.mp (hle hD)
  simpa [RHTower.finiteHankelMaximalMinorOver, hM, Matrix.submatrix_id_id] using this

/-- **Points of `V_s` are singular points of `V_{s+1}`.** -/
theorem zariskiTangent_hankel_eq_top {N s : ℕ} (p : Fin N → K)
    (hp : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N s, eval p g = 0) :
    zariskiTangent (RHTower.finiteHankelSecantIdeal K N (s + 1)) p = ⊤ :=
  zariskiTangent_eq_top_of_le_sqIdeal (secantIdeal_le_sqIdeal K p hp)

/-! ## The bordered minors -/

/-- The bordered minor with columns `0, …, r−1, n−r`. -/
def borderMinor (N r n : ℕ) (hn : 2 * r ≤ n) (hnN : n < N) : MvPolynomial (Fin N) K :=
  RHTower.finiteHankelMaximalMinorOver K (borderCols r n) (fun j => by
    unfold borderCols; split_ifs <;> omega)

theorem borderMinor_mem {N r n : ℕ} (hn : 2 * r ≤ n) (hnN : n < N) :
    borderMinor K N r n hn hnN ∈ RHTower.finiteHankelSecantIdeal K N r :=
  Ideal.subset_span ⟨_, _, borderCols_strictMono hn, rfl⟩

theorem borderCols_index_le {r n : ℕ} (hn : 2 * r ≤ n) (k j : Fin (r + 1)) :
    (k : ℕ) + borderCols r n j ≤ n := by
  have := k.isLt; have := j.isLt; unfold borderCols; split_ifs <;> omega

/-- `∂g_n/∂x_m = 0` for `m > n`. -/
theorem pderiv_borderMinor_of_lt {N r n : ℕ} (hn : 2 * r ≤ n) (hnN : n < N) {m : Fin N}
    (hm : n < m) : pderiv m (borderMinor K N r n hn hnN) = 0 := by
  classical
  rw [borderMinor, RHTower.finiteHankelMaximalMinorOver, derivation_det]
  refine Finset.sum_eq_zero fun k _ => Matrix.det_eq_zero_of_row_eq_zero k fun j => ?_
  rw [Matrix.updateRow_self, pderiv_X, Pi.single_apply, if_neg]
  intro h
  have := congrArg Fin.val h
  simp only [RHTower.finiteHankelIndex] at this
  have := borderCols_index_le hn k j
  omega

/-- `∂g_n/∂x_n = δ`, the leading `r × r` minor. -/
theorem pderiv_borderMinor_self {N r n : ℕ} (hn : 2 * r ≤ n) (hnN : n < N) :
    pderiv ⟨n, hnN⟩ (borderMinor K N r n hn hnN) = hankelLeadMinor K N r := by
  classical
  rw [borderMinor, RHTower.finiteHankelMaximalMinorOver, derivation_det,
    Finset.sum_eq_single (Fin.last r)]
  · rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.updateRow_self, pderiv_X, Pi.single_apply, if_pos, Fin.succAbove_last]
      · rw [hankelLeadMinor, mul_one, Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow,
          one_mul]
        congr 1
        refine Matrix.ext fun i j => ?_
        rw [Matrix.submatrix_apply, Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne,
          Matrix.of_apply, hankelCoord, dif_pos (by have := i.isLt; have := j.isLt; omega)]
        congr 1
        ext
        simp [RHTower.finiteHankelIndex, borderCols, j.isLt]
      · ext
        simp [RHTower.finiteHankelIndex, borderCols]
        omega
    · intro j _ hj
      rw [Matrix.updateRow_self, pderiv_X, Pi.single_apply, if_neg, mul_zero, zero_mul]
      intro h
      have := congrArg Fin.val h
      simp only [RHTower.finiteHankelIndex, Fin.val_last, borderCols] at this
      have hj' : (j : ℕ) < r := by
        have := Fin.val_lt_last hj
        simpa using this
      rw [if_pos hj'] at this
      omega
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    refine Matrix.det_eq_zero_of_row_eq_zero k fun j => ?_
    rw [Matrix.updateRow_self, pderiv_X, Pi.single_apply, if_neg]
    intro h
    have hidx := congrArg Fin.val h
    simp only [RHTower.finiteHankelIndex] at hidx
    have hk' : (k : ℕ) < r := by
      have := Fin.val_lt_last hk
      simpa using this
    have hj := j.isLt
    unfold borderCols at hidx
    split_ifs at hidx <;> omega
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## The tangent space in the leading chart -/

/-- Evaluation of the secant ring at a point of the secant variety. -/
def secantEval {N r : ℕ} (y : Fin N → K)
    (hy : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N r, eval y g = 0) :
    HankelSecantRing K N r →+* K :=
  Ideal.Quotient.lift _ (eval y) hy

/-- **A tangent vector at a point of the leading chart is determined by its first `2r`
coordinates.** -/
theorem eq_zero_of_mem_zariskiTangent_lead {N r : ℕ} {y : Fin N → K}
    (hδ : eval y (hankelLeadMinor K N r) ≠ 0) {v : Fin N → K}
    (hv : v ∈ zariskiTangent (RHTower.finiteHankelSecantIdeal K N r) y)
    (h0 : ∀ j : Fin N, (j : ℕ) < 2 * r → v j = 0) : v = 0 := by
  classical
  suffices H : ∀ n (hnN : n < N), v ⟨n, hnN⟩ = 0 from funext fun m => H m m.isLt
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hnN
    by_cases hn : n < 2 * r
    · exact h0 _ hn
    push Not at hn
    have hg := hv _ (borderMinor_mem K hn hnN)
    rw [tangentDeriv, Finset.sum_eq_single ⟨n, hnN⟩, pderiv_borderMinor_self] at hg
    · exact (mul_eq_zero.mp hg).resolve_right hδ
    · intro m _ hm
      rcases lt_or_gt_of_ne (fun h : (m : ℕ) = n => hm (Fin.ext h)) with hlt | hgt
      · rw [ih m hlt m.isLt, zero_mul]
      · rw [pderiv_borderMinor_of_lt K hn hnN hgt, map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **Every choice of the first `2r` coordinates is a tangent vector** at a point of the leading
chart: evaluate the chart `A_δ ≅ K[y]_δ` at `y + ε e_k`. -/
theorem exists_mem_zariskiTangent_lead [CharZero K] {N r : ℕ} (hrN : 2 * r ≤ N) {y : Fin N → K}
    (hy : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N r, eval y g = 0)
    (hδ : eval y (hankelLeadMinor K N r) ≠ 0) (k : Fin (2 * r)) :
    ∃ v ∈ zariskiTangent (RHTower.finiteHankelSecantIdeal K N r) y,
      ∀ j : Fin (2 * r), v (Fin.castLE hrN j) = if j = k then 1 else 0 := by
  classical
  set A := HankelSecantRing K N r
  set δ' := hankelLeadMinor K (2 * r) r with hδ'def
  set yr : Fin (2 * r) → K := fun j => y (Fin.castLE hrN j)
  set Ψ : MvPolynomial (Fin (2 * r)) K →ₐ[K] TrivSqZeroExt K K :=
    aeval (dualNumberPoint yr fun j => if j = k then 1 else 0) with hΨ
  have hcoord : ∀ j : Fin (2 * r), hankelCoord K N j = X (Fin.castLE hrN j) := fun j => by
    rw [hankelCoord, dif_pos (by omega)]; rfl
  have hδ'eval : eval yr δ' = eval y (hankelLeadMinor K N r) := by
    rw [hδ'def, hankelLeadMinor, hankelLeadMinor, RingHom.map_det, RingHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    have hij : (i : ℕ) + j < 2 * r := by have := i.isLt; have := j.isLt; omega
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hankelCoord,
      dif_pos hij, dif_pos (lt_of_lt_of_le hij hrN), eval_X, yr]
    rfl
  have hΨunit : IsUnit (Ψ δ') := by
    rw [hΨ, aeval_dualNumberPoint, TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_add, fst_inl, fst_inr,
      add_zero, isUnit_iff_ne_zero, hδ'eval]
    exact hδ
  set L : Localization.Away δ' →+* TrivSqZeroExt K K :=
    IsLocalization.Away.lift δ' (g := Ψ.toRingHom) hΨunit with hL
  have hLalg : ∀ q, L (algebraMap _ (Localization.Away δ') q) = Ψ q := by
    intro q
    rw [hL, IsLocalization.Away.lift, IsLocalization.lift_eq]
    rfl
  set χ := hankelChartEquiv K hrN with hχ
  have hχalg : ∀ q, χ (algebraMap _ (Localization.Away δ') q) =
      algebraMap A _ (hankelChartHom K N r q) := fun q => hankelChartLoc_algebraMap K N r q
  set ψ : A →+* TrivSqZeroExt K K :=
    L.comp (χ.symm.toRingHom.comp (algebraMap A (Localization.Away (hankelChartElem K N r))))
    with hψdef
  have hψalg : ∀ q, ψ (hankelChartHom K N r q) = Ψ q := by
    intro q
    rw [hψdef, RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, ← hχalg, RingEquiv.symm_apply_apply, hLalg]
  -- the first-order part agrees with evaluation at `y`
  set ev := secantEval K y hy with hev
  have hevmk : ∀ g, ev (Ideal.Quotient.mk _ g) = eval y g := fun g => rfl
  have hevδ : IsUnit (ev (hankelChartElem K N r)) := by
    rw [hankelChartElem_eq, hevmk, isUnit_iff_ne_zero]; exact hδ
  set evL : Localization.Away (hankelChartElem K N r) →+* K :=
    IsLocalization.Away.lift (hankelChartElem K N r) (g := ev) hevδ with hevL
  have hevLalg : ∀ a, evL (algebraMap A _ a) = ev a := by
    intro a
    rw [hevL, IsLocalization.Away.lift, IsLocalization.lift_eq]
  have hfst : (TrivSqZeroExt.fstHom K K K).toRingHom.comp L = evL.comp χ.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers δ')
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hLalg,
        RingEquiv.toRingHom_eq_coe, hχalg, hevLalg, hΨ, aeval_C, TrivSqZeroExt.algebraMap_eq_inl,
        TrivSqZeroExt.fstHom_apply, fst_inl, hankelChartHom]
      rw [show (algebraMap K A c) = Ideal.Quotient.mk _ (C c) from rfl, hevmk, eval_C]
    · intro j
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hLalg,
        RingEquiv.toRingHom_eq_coe, hχalg, hevLalg, hΨ, aeval_X, TrivSqZeroExt.fstHom_apply,
        dualNumberPoint, fst_add, fst_inl, fst_inr, add_zero, hankelChartHom, hcoord, hevmk, eval_X, yr]
  have hfstψ : ∀ a : A, (ψ a).fst = ev a := by
    intro a
    have := congrArg (fun φ : Localization.Away δ' →+* K =>
      φ (χ.symm (algebraMap A (Localization.Away (hankelChartElem K N r)) a))) hfst
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.apply_symm_apply,
      hevLalg] at this
    exact this
  -- the tangent vector
  set v : Fin N → K := fun n => (ψ (Ideal.Quotient.mk _ (X n))).snd with hv
  have hψmk : ψ.comp (Ideal.Quotient.mk _) = (aeval (dualNumberPoint y v)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have h1 := hψalg (C c)
      rw [hankelChartHom, aeval_C] at h1
      rw [RingHom.comp_apply, show Ideal.Quotient.mk (RHTower.finiteHankelSecantIdeal K N r) (C c)
        = algebraMap K A c from rfl, h1]
      simp [hΨ]
    · intro n
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, dualNumberPoint,
        ← TrivSqZeroExt.inl_fst_add_inr_snd_eq (ψ (Ideal.Quotient.mk _ (X n))), hfstψ, hevmk,
        eval_X]
  refine ⟨v, fun g hg => ?_, fun j => ?_⟩
  · have h0 : ψ (Ideal.Quotient.mk _ g) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
    have h1 := congrArg (fun φ : MvPolynomial (Fin N) K →+* TrivSqZeroExt K K => φ g) hψmk
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0,
      aeval_dualNumberPoint] at h1
    have := congrArg TrivSqZeroExt.snd h1
    simpa using this.symm
  · have h1 := hψalg (X j)
    rw [hankelChartHom, aeval_X, hcoord] at h1
    rw [hv]
    simp only
    rw [h1, hΨ, aeval_X, dualNumberPoint, snd_add, snd_inl, snd_inr, zero_add]

/-- **The tangent space at a point of the leading chart has dimension `2r`.** -/
theorem finrank_zariskiTangent_lead [CharZero K] {N r : ℕ} (hrN : 2 * r ≤ N) {y : Fin N → K}
    (hy : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N r, eval y g = 0)
    (hδ : eval y (hankelLeadMinor K N r) ≠ 0) :
    Module.finrank K (zariskiTangent (RHTower.finiteHankelSecantIdeal K N r) y) = 2 * r := by
  classical
  set T := zariskiTangent (RHTower.finiteHankelSecantIdeal K N r) y
  set π : T →ₗ[K] (Fin (2 * r) → K) :=
    (LinearMap.funLeft K K (Fin.castLE hrN)).comp T.subtype with hπ
  have hinj : Function.Injective π := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : (v : Fin N → K) = 0 := by
      refine eq_zero_of_mem_zariskiTangent_lead K hδ v.2 fun j hj => ?_
      have := congrFun hv ⟨j, hj⟩
      simpa [hπ, LinearMap.funLeft_apply] using this
    exact Subtype.ext h0
  choose v hvT hvk using fun k => exists_mem_zariskiTangent_lead K hrN hy hδ k
  have hsurj : Function.Surjective π := by
    intro w
    refine ⟨⟨∑ k, w k • v k, T.sum_mem fun k _ => T.smul_mem _ (hvT k)⟩, ?_⟩
    funext j
    simp only [hπ, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.funLeft_apply,
      Finset.sum_apply, Pi.smul_apply, hvk, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [(LinearEquiv.ofBijective π ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fin_fun]

/-- **Points off `V_s` are smooth points of `V_{s+1}`**: the Zariski tangent space has dimension
`2(s+1) = dim V_{s+1}`. -/
theorem finrank_zariskiTangent_hankel [CharZero K] {N s : ℕ} (hsN : 2 * (s + 1) < N)
    (p : Fin N → K) (hp : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N (s + 1), eval p g = 0)
    (hsing : ∃ g ∈ RHTower.finiteHankelSecantIdeal K N s, eval p g ≠ 0) :
    Module.finrank K (zariskiTangent (RHTower.finiteHankelSecantIdeal K N (s + 1)) p) =
      2 * (s + 1) := by
  classical
  set I := RHTower.finiteHankelSecantIdeal K N (s + 1)
  -- the maximal minors at `p`
  have hmin : ∀ (c : Fin (s + 1 + 1) → ℕ) (hbound : ∀ j, (s + 1 + 1) + c j ≤ N), StrictMono c →
      Matrix.det (fun i j : Fin (s + 1 + 1) => p (RHTower.finiteHankelIndex c hbound i j)) = 0 := by
    intro c hbound hc
    have := hp _ (Ideal.subset_span ⟨c, hbound, hc, rfl⟩)
    rw [RHTower.finiteHankelMaximalMinorOver, RingHom.map_det] at this
    convert this using 2
    ext i j
    simp
  obtain ⟨c, hbound, hc, hcp⟩ : ∃ (c : Fin (s + 1) → ℕ) (hbound : ∀ j, (s + 1) + c j ≤ N),
      StrictMono c ∧ eval p (RHTower.finiteHankelMaximalMinorOver K c hbound) ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨g, hg, hgp⟩ := hsing
    apply hgp
    have hle : RHTower.finiteHankelSecantIdeal K N s ≤ RingHom.ker (eval p) := by
      rw [RHTower.finiteHankelSecantIdeal, Ideal.span_le]
      rintro _ ⟨c, hbound, hc, rfl⟩
      exact hall c hbound hc
    exact hle hg
  have hdet : Matrix.det (fun i j : Fin (s + 1) => p (RHTower.finiteHankelIndex c hbound i j)) ≠
      0 := by
    rw [RHTower.finiteHankelMaximalMinorOver, RingHom.map_det] at hcp
    convert hcp using 3
    ext i
    simp
  obtain ⟨t, -, ht⟩ := exists_chartPoint_det_ne_zero p hsN hmin c hbound hdet
  -- move the chart
  set σ := momentChartEquiv K N (t : K)
  have hmap : I.map σ = I := map_momentChartEquiv_secantIdeal K N (s + 1) (t : K)
  have hI : ∀ g ∈ I, σ g ∈ I := fun g hg => by
    rw [← hmap]; exact Ideal.mem_map_of_mem _ hg
  have hI' : ∀ g ∈ I, σ.symm g ∈ I := fun g hg => by
    rw [← hmap] at hg
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ σ.surjective).mp hg
    rwa [AlgEquiv.symm_apply_apply]
  rw [finrank_zariskiTangent_eq_of_algEquiv σ hI hI' p]
  set y := mapPoint σ.toAlgHom p with hy
  have hyval : ∀ g, eval y g = eval p (σ g) := fun g =>
    ((tangentDeriv_map σ.toAlgHom p 0 g).1).symm
  have hyI : ∀ g ∈ I, eval y g = 0 := fun g hg => by rw [hyval]; exact hp _ (hI g hg)
  have hyδ : eval y (hankelLeadMinor K N (s + 1)) ≠ 0 := by
    rw [hyval]
    have := map_momentChartEquiv_leadMinor (eval p) (r := s + 1) hsN.le (t : K)
    simp only [eval_X, eval_C] at this
    rw [show (σ (hankelLeadMinor K N (s + 1))) =
      momentChartEquiv K N (t : K) (hankelLeadMinor K N (s + 1)) from rfl, this]
    convert ht using 3
  exact finrank_zariskiTangent_lead K hsN.le hyI hyδ

end

end GaloisForLFunctions.HTGeometry
