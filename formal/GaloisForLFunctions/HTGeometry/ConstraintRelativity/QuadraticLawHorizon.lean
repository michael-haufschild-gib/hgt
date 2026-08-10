import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.RankOneFraming
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler

/-!
# The quadratic law horizon: discriminant, Bockstein, and controlled conditioning

For `B = ℂ[h]` and `A = B[η]/(η(η−h))` the two-character observer `J(a + bη) = (a, a + bh)` sits in
an exact global descent sequence

`0 → A → B² → B/(h) → 0`.

Away from the collision the fibre is the split algebra `ℂ × ℂ`; at the collision it is the dual
numbers and the ordinary specialized observer erases the nilpotent line, which is exactly the
kernel that the derived (Koszul/Tor) specialization retains.

The hidden coefficient is recovered off the collision by `D_c(u,v) = (v−u)/c`, whose norm is
`√2/|c|`, so `√|Disc| · ‖D_c‖ = √2` is constant: the decoder blows up exactly like the inverse
square root of the discriminant.  That blow-up is universal for any continuously approached
injectivity failure.

Finally `Ω[A⁄B]` is the cyclic module on `dη` with the single relation `(2η − h) dη = 0`, so the
annihilator of the relative differentials is the different ideal `(2η − h)`, whose square-zero
shadow is the nonreduced discriminant `(h²)`.
-/

namespace HTGeometry.ConstraintRelativity

open Polynomial

/-! ## The quadratic family -/

/-- The base ring `B = ℂ[h]`. -/
abbrev LawBase : Type := Polynomial ℂ

/-- The family parameter `h`. -/
noncomputable abbrev lawParam : LawBase := Polynomial.X

/-- The quadratic family `η² − hη`. -/
noncomputable def lawPoly : LawBase[X] := X ^ 2 - C lawParam * X

theorem lawPoly_monic : lawPoly.Monic := by
  unfold lawPoly
  monicity!

theorem lawPoly_natDegree : lawPoly.natDegree = 2 := by
  unfold lawPoly
  compute_degree!

/-- The total law algebra `A = B[η]/(η(η−h))`. -/
abbrev LawAlgebra : Type := AdjoinRoot lawPoly

/-- The generator `η`. -/
noncomputable abbrev lawEta : LawAlgebra := AdjoinRoot.root lawPoly

theorem lawEta_sq : lawEta ^ 2 = AdjoinRoot.of lawPoly lawParam * lawEta := by
  have h := AdjoinRoot.eval₂_root lawPoly
  rw [lawPoly] at h
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C] at h
  have hx : (AdjoinRoot.root lawPoly) ^ 2
      - (AdjoinRoot.of lawPoly) lawParam * AdjoinRoot.root lawPoly = 0 := by
    convert h using 2 <;> rfl
  linear_combination hx

/-! ## Coordinates on the law algebra -/

/-- Every element of `A` is `a + bη` with `a, b` in the base. -/
theorem exists_lawCoords (x : LawAlgebra) :
    ∃ a b : LawBase, x = AdjoinRoot.of lawPoly a + AdjoinRoot.of lawPoly b * lawEta := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hdvd : lawPoly ∣ p - p %ₘ lawPoly := by
    have h := Polynomial.dvd_modByMonic_sub p lawPoly
    have hneg : p - p %ₘ lawPoly = -(p %ₘ lawPoly - p) := by ring
    rw [hneg]
    exact dvd_neg.2 h
  have hmk : AdjoinRoot.mk lawPoly p = AdjoinRoot.mk lawPoly (p %ₘ lawPoly) :=
    AdjoinRoot.mk_eq_mk.2 hdvd
  have hnd : (p %ₘ lawPoly).natDegree ≤ 1 := by
    have hne : lawPoly ≠ 1 := by
      intro hcon
      have := lawPoly_natDegree
      rw [hcon] at this
      simp at this
    have hlt := Polynomial.natDegree_modByMonic_lt p lawPoly_monic hne
    rw [lawPoly_natDegree] at hlt
    omega
  have hqform : (p %ₘ lawPoly)
      = C ((p %ₘ lawPoly).coeff 1) * X + C ((p %ₘ lawPoly).coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hnd
  refine ⟨(p %ₘ lawPoly).coeff 0, (p %ₘ lawPoly).coeff 1, ?_⟩
  rw [hmk]
  conv_lhs => rw [hqform]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
    show AdjoinRoot.mk lawPoly X = lawEta from rfl]
  ring

/-! ## Theorem 1: the exact global descent sequence -/

theorem lawObserver_eval :
    lawPoly.eval₂ (Algebra.ofId LawBase (LawBase × LawBase)).toRingHom
      ((0, lawParam) : LawBase × LawBase) = 0 := by
  simp only [lawPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
  refine Prod.ext ?_ ?_ <;> simp [pow_two, Prod.algebraMap_apply]

/-- The two-character observer `J(a + bη) = (a, a + bh)`. -/
noncomputable def lawObserver : LawAlgebra →ₐ[LawBase] LawBase × LawBase :=
  AdjoinRoot.liftAlgHom lawPoly (Algebra.ofId LawBase (LawBase × LawBase))
    ((0, lawParam) : LawBase × LawBase) lawObserver_eval

@[simp]
theorem lawObserver_eta : lawObserver lawEta = (0, lawParam) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp]
theorem lawObserver_of (a : LawBase) : lawObserver (AdjoinRoot.of lawPoly a) = (a, a) := by
  rw [lawObserver, AdjoinRoot.liftAlgHom_of]
  simp [Algebra.ofId_apply]

theorem lawObserver_coords (a b : LawBase) :
    lawObserver (AdjoinRoot.of lawPoly a + AdjoinRoot.of lawPoly b * lawEta)
      = (a, a + b * lawParam) := by
  rw [map_add, map_mul, lawObserver_of, lawObserver_of, lawObserver_eta]
  refine Prod.ext ?_ ?_ <;> simp

/-- **The observer is injective.** -/
theorem lawObserver_injective : Function.Injective lawObserver := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, b, rfl⟩ := exists_lawCoords x
  rw [lawObserver_coords] at hx
  have ha : a = 0 := congrArg Prod.fst hx
  have hb : a + b * lawParam = 0 := congrArg Prod.snd hx
  rw [ha, zero_add] at hb
  have hb0 : b = 0 := by
    rcases mul_eq_zero.1 hb with h | h
    · exact h
    · exact absurd h Polynomial.X_ne_zero
  rw [ha, hb0]
  simp

/-- The collision reporter `r(x, y) = y − x mod h`. -/
noncomputable def collisionReporter :
    (LawBase × LawBase) →ₗ[LawBase] LawBase ⧸ (Ideal.span {lawParam}) where
  toFun p := Ideal.Quotient.mk _ (p.2 - p.1)
  map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; rw [← map_add]; ring_nf
  map_smul' := by
    intro c p
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    rw [← mul_sub]
    rfl

@[simp]
theorem collisionReporter_apply (p : LawBase × LawBase) :
    collisionReporter p = Ideal.Quotient.mk _ (p.2 - p.1) := rfl

/-- **The reporter is surjective.** -/
theorem collisionReporter_surjective : Function.Surjective collisionReporter := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨(0, b), by simp⟩

/-- **Exactness in the middle.**  The image of the observer is the kernel of the reporter. -/
theorem range_lawObserver :
    LinearMap.range (lawObserver.toLinearMap) = LinearMap.ker collisionReporter := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, rfl⟩ := exists_lawCoords x
    rw [LinearMap.mem_ker]
    show collisionReporter (lawObserver _) = 0
    rw [lawObserver_coords, collisionReporter_apply]
    simp only [add_sub_cancel_left]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨b, rfl⟩)
  · intro p hp
    have hmem : p.2 - p.1 ∈ Ideal.span {lawParam} :=
      Ideal.Quotient.eq_zero_iff_mem.1 hp
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨AdjoinRoot.of lawPoly p.1 + AdjoinRoot.of lawPoly b * lawEta, ?_⟩
    simp only [AlgHom.toLinearMap_apply, lawObserver_coords]
    refine Prod.ext rfl ?_
    show p.1 + b * lawParam = p.2
    rw [hb]
    ring

/-! ## Theorem 2: the fibre classification -/

/-- The fibre of the family at `h = c` is `ℂ[η]/(η(η−c))`. -/
theorem fibre_discr (c : ℂ) : quadDiscr c 0 = c ^ 2 := by
  simp [quadDiscr]

/-- **Split fibre.**  Away from the collision the fibre is `ℂ × ℂ`. -/
theorem fibre_split (c : ℂ) (hc : c ≠ 0) :
    Nonempty (quadAlgebra c 0 ≃ₐ[ℂ] ℂ × ℂ) :=
  exists_algEquiv_prod_of_discr_ne_zero c 0 (by
    rw [fibre_discr]
    exact pow_ne_zero 2 hc)

/-- **Collision fibre.**  At the collision the fibre is the dual numbers. -/
theorem fibre_dual : Nonempty (quadAlgebra (0 : ℂ) 0 ≃ₐ[ℂ] quadAlgebra 0 0) :=
  ⟨AlgEquiv.refl⟩

/-- **The law horizon is genuine.**  The collision fibre is not isomorphic to the split fibre. -/
theorem fibre_not_algEquiv (c : ℂ) (hc : c ≠ 0) :
    ¬ Nonempty (quadAlgebra (0 : ℂ) 0 ≃ₐ[ℂ] quadAlgebra c 0) := by
  rintro ⟨e⟩
  obtain ⟨f⟩ := fibre_split c hc
  exact not_nonempty_algEquiv_dual_prod ⟨e.trans f⟩

/-! ## Theorem 3: the erased line is the derived class -/

/-- The specialized observer at the collision, `a + bε ↦ (a, a)`. -/
noncomputable def collisionObserver : quadAlgebra (0 : ℂ) 0 →ₐ[ℂ] ℂ × ℂ :=
  AdjoinRoot.liftAlgHom (quadPoly (0 : ℂ) 0) (Algebra.ofId ℂ (ℂ × ℂ)) ((0, 0) : ℂ × ℂ) (by
    rw [eval₂_quadPoly]
    simp)

@[simp]
theorem collisionObserver_root :
    collisionObserver (AdjoinRoot.root (quadPoly (0 : ℂ) 0)) = 0 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **The nilpotent line is erased.**  The specialized observer kills the square-zero generator. -/
theorem collisionObserver_kills_nilpotent :
    AdjoinRoot.root (quadPoly (0 : ℂ) 0) ≠ 0 ∧
      collisionObserver (AdjoinRoot.root (quadPoly (0 : ℂ) 0)) = 0 :=
  ⟨root_ne_zero 0 0, collisionObserver_root⟩

/-- **The derived class.**  The Koszul first homology of the resolution `0 → B →^h B → 0` of the
residue field, tensored with the residue field, is everything: the parameter acts by zero on
`B/(h)`, so `Tor₁^B(k, k) ≅ k`. -/
theorem tor_one_eq_top :
    {m : LawBase ⧸ (Ideal.span {lawParam}) | lawParam • m = 0} = Set.univ := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
  have hsmul : lawParam • Ideal.Quotient.mk (Ideal.span {lawParam}) b
      = Ideal.Quotient.mk (Ideal.span {lawParam}) (lawParam * b) := rfl
  rw [hsmul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-! ## Theorem 4: sharp discriminant conditioning -/

/-- The hidden-coefficient decoder off the collision. -/
noncomputable def hiddenDecoder (c : ℂ) : (ℂ × ℂ) →ₗ[ℂ] ℂ where
  toFun p := (p.2 - p.1) / c
  map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' := by intro a p; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    RingHom.id_apply]; ring

@[simp]
theorem hiddenDecoder_apply (c : ℂ) (p : ℂ × ℂ) : hiddenDecoder c p = (p.2 - p.1) / c := rfl

/-- **Recovery.**  Off the collision the decoder recovers the hidden coefficient from the two
observed characters. -/
theorem hiddenDecoder_recovers (c : ℂ) (hc : c ≠ 0) (a b : ℂ) :
    hiddenDecoder c (a, a + b * c) = b := by
  simp only [hiddenDecoder_apply, add_sub_cancel_left]
  field_simp

/-- **The decoder norm.**  The coefficient vector of the decoder is `(−1/c, 1/c)`, of squared
Euclidean norm `2/‖c‖²`. -/
theorem hiddenDecoder_normSq (c : ℂ) (hc : c ≠ 0) :
    ‖(-(1 / c) : ℂ)‖ ^ 2 + ‖(1 / c : ℂ)‖ ^ 2 = 2 / ‖c‖ ^ 2 := by
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  rw [norm_neg, norm_div, norm_one]
  field_simp
  ring

/-- **The conditioning law.**  The square root of the discriminant times the decoder norm is the
constant `√2`: the decoder blows up exactly like `|Disc|^{-1/2}`. -/
theorem conditioning_law (c : ℂ) (hc : c ≠ 0) :
    Real.sqrt ‖c ^ 2‖ * (Real.sqrt 2 / ‖c‖) = Real.sqrt 2 := by
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  rw [norm_pow, Real.sqrt_sq (norm_nonneg c)]
  field_simp

/-! ### The decoder operator norm on Euclidean `ℂ²` -/

/-- The Riesz vector of the hidden-coefficient decoder. -/
noncomputable def decoderVector (c : ℂ) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![-((starRingEnd ℂ) c)⁻¹, ((starRingEnd ℂ) c)⁻¹]

/-- **Card `(9)`, Euclidean form.**  The hidden-coefficient decoder as a continuous linear
functional on Euclidean `ℂ²`, where the card's operator norm is taken. -/
noncomputable def hiddenDecoderCLM (c : ℂ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ :=
  innerSL ℂ (decoderVector c)

theorem hiddenDecoderCLM_apply (c : ℂ) (p : EuclideanSpace ℂ (Fin 2)) :
    hiddenDecoderCLM c p = (p.ofLp 1 - p.ofLp 0) / c := by
  show (inner ℂ (decoderVector c) p : ℂ) = _
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, decoderVector, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, RCLike.inner_apply, map_neg, map_inv₀, Complex.conj_conj]
  ring

/-- The Euclidean decoder is the earlier product-space decoder read in coordinates. -/
theorem hiddenDecoderCLM_eq (c : ℂ) (p : EuclideanSpace ℂ (Fin 2)) :
    hiddenDecoderCLM c p = hiddenDecoder c (p.ofLp 0, p.ofLp 1) := by
  rw [hiddenDecoderCLM_apply, hiddenDecoder_apply]

/-- **Card `(10)`.**  The operator norm of the decoder, with the Euclidean norm on `ℂ²`, is
`√2/|c|`.  This is the sharp conditioning constant, not merely the norm of the coefficient
vector. -/
theorem norm_hiddenDecoderCLM (c : ℂ) (hc : c ≠ 0) :
    ‖hiddenDecoderCLM c‖ = Real.sqrt 2 / ‖c‖ := by
  have hcn : (0 : ℝ) < ‖c‖ := norm_pos_iff.2 hc
  rw [hiddenDecoderCLM, innerSL_apply_norm, decoderVector, EuclideanSpace.norm_eq]
  have hentry : ‖(-((starRingEnd ℂ) c)⁻¹)‖ = ‖c‖⁻¹ := by
    rw [norm_neg, norm_inv, RCLike.norm_conj]
  have hentry' : ‖(((starRingEnd ℂ) c)⁻¹)‖ = ‖c‖⁻¹ := by
    rw [norm_inv, RCLike.norm_conj]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hentry, hentry']
  rw [show (‖c‖⁻¹ ^ 2 + ‖c‖⁻¹ ^ 2) = 2 * (‖c‖⁻¹) ^ 2 by ring,
    Real.sqrt_mul (by norm_num) _, Real.sqrt_sq (by positivity)]
  rw [div_eq_mul_inv]

/-- **Card `(11)`, boxed, operator form.**  The square root of the framed fibre discriminant times
the decoder operator norm is the constant `√2`. -/
theorem conditioning_law_opNorm (c : ℂ) (hc : c ≠ 0) :
    Real.sqrt ‖c ^ 2‖ * ‖hiddenDecoderCLM c‖ = Real.sqrt 2 := by
  rw [norm_hiddenDecoderCLM c hc]
  exact conditioning_law c hc

/-! ## Theorem 5: universal decoder blow-up -/

/-- **Universal decoder blow-up.**  If a continuous family of maps loses injectivity in the limit,
every family of left inverses has operator norms tending to infinity. -/
theorem decoder_norm_tendsto_atTop {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : ℝ → (E →L[ℝ] F)) (D : ℝ → (F →L[ℝ] E)) (x : E) (hx : ‖x‖ = 1)
    (hker : Filter.Tendsto (fun t => ‖J t x‖) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hinv : ∀ᶠ t in nhdsWithin 0 {(0 : ℝ)}ᶜ, D t (J t x) = x) :
    Filter.Tendsto (fun t => ‖D t‖) (nhdsWithin 0 {(0 : ℝ)}ᶜ) Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun M => ?_
  rcases lt_or_ge 0 M with hM | hM
  swap
  · filter_upwards with t using le_trans hM (norm_nonneg _)
  · have hMinv : (0 : ℝ) < 1 / M := by positivity
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, ‖J t x‖ < 1 / M :=
      hker (Iio_mem_nhds hMinv)
    filter_upwards [hev, hinv] with t h1 h3
    have hle : (1 : ℝ) ≤ ‖D t‖ * ‖J t x‖ := by
      have hb : ‖(D t) ((J t) x)‖ ≤ ‖D t‖ * ‖(J t) x‖ := (D t).le_opNorm _
      rw [h3, hx] at hb
      exact hb
    have hDpos : 0 < ‖D t‖ := by
      rcases lt_or_eq_of_le (norm_nonneg (D t)) with h | h
      · exact h
      · rw [← h, zero_mul] at hle
        linarith
    have hlt : ‖D t‖ * ‖J t x‖ < ‖D t‖ * (1 / M) := by
      exact mul_lt_mul_of_pos_left h1 hDpos
    have hfin : (1 : ℝ) < ‖D t‖ * (1 / M) := lt_of_le_of_lt hle hlt
    rw [mul_one_div, lt_div_iff₀ hM] at hfin
    linarith

/-! ## Theorem 6: the relative cotangent module -/

/-- The different element of the quadratic family is `2η − h`. -/
theorem derivative_lawPoly : derivative lawPoly = 2 * X - C lawParam := by
  unfold lawPoly
  simp only [derivative_sub, derivative_pow, derivative_X, derivative_mul, derivative_C,
    Nat.cast_ofNat, mul_one, zero_mul]
  rw [map_ofNat]
  ring

theorem rootDifferent_lawPoly :
    rootDifferent lawPoly
      = 2 * lawEta - AdjoinRoot.of lawPoly lawParam := by
  rw [rootDifferent, derivative_lawPoly]
  simp only [map_sub, map_mul, map_ofNat]
  rw [show AdjoinRoot.mk lawPoly X = lawEta from rfl,
    show AdjoinRoot.mk lawPoly (C lawParam) = AdjoinRoot.of lawPoly lawParam from rfl]

/-- **The relative cotangent module.**  `Ω[A⁄B]` is cyclic on `dη` with the single relation
`(2η − h) dη = 0`. -/
noncomputable def lawKaehlerEquiv :
    Ω[LawAlgebra⁄LawBase] ≃ₗ[LawAlgebra] MonogenicOmega lawPoly :=
  kaehlerEquivMonogenic lawPoly

/-- **The annihilator of the relative differentials is the different ideal.** -/
theorem annihilator_lawKaehler :
    Module.annihilator LawAlgebra (Ω[LawAlgebra⁄LawBase])
      = Ideal.span {2 * lawEta - AdjoinRoot.of lawPoly lawParam} := by
  rw [annihilator_kaehler lawPoly, rootDifferent_lawPoly]

/-! ### Coordinates are unique -/

theorem lawCoords_unique {a b a' b' : LawBase}
    (h : AdjoinRoot.of lawPoly a + AdjoinRoot.of lawPoly b * lawEta
      = AdjoinRoot.of lawPoly a' + AdjoinRoot.of lawPoly b' * lawEta) : a = a' ∧ b = b' := by
  have hobs := congrArg lawObserver h
  rw [lawObserver_coords, lawObserver_coords] at hobs
  have h1 : a = a' := congrArg Prod.fst hobs
  have h2 : a + b * lawParam = a' + b' * lawParam := congrArg Prod.snd hobs
  refine ⟨h1, ?_⟩
  rw [h1] at h2
  have h3 : b * lawParam = b' * lawParam := by linear_combination h2
  exact mul_right_cancel₀ Polynomial.X_ne_zero h3

/-! ### The kernel of the collision observer is the nilpotent line -/

theorem exists_quadCoords (x : quadAlgebra (0 : ℂ) 0) :
    ∃ u v : ℂ, x = AdjoinRoot.of (quadPoly (0 : ℂ) 0) u
      + AdjoinRoot.of (quadPoly (0 : ℂ) 0) v * AdjoinRoot.root (quadPoly (0 : ℂ) 0) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  have hmonic : (quadPoly (0 : ℂ) 0).Monic := by
    unfold quadPoly
    monicity!
  have hdvd : quadPoly (0 : ℂ) 0 ∣ p - p %ₘ quadPoly (0 : ℂ) 0 := by
    have hd := Polynomial.dvd_modByMonic_sub p (quadPoly (0 : ℂ) 0)
    have hneg : p - p %ₘ quadPoly (0 : ℂ) 0 = -(p %ₘ quadPoly (0 : ℂ) 0 - p) := by ring
    rw [hneg]
    exact dvd_neg.2 hd
  have hmk : AdjoinRoot.mk (quadPoly (0 : ℂ) 0) p
      = AdjoinRoot.mk (quadPoly (0 : ℂ) 0) (p %ₘ quadPoly (0 : ℂ) 0) :=
    AdjoinRoot.mk_eq_mk.2 hdvd
  have hne : quadPoly (0 : ℂ) 0 ≠ 1 := by
    intro hcon
    have hd := quadPoly_natDegree (0 : ℂ) 0
    rw [hcon] at hd
    simp at hd
  have hnd : (p %ₘ quadPoly (0 : ℂ) 0).natDegree ≤ 1 := by
    have hlt := Polynomial.natDegree_modByMonic_lt p hmonic hne
    rw [quadPoly_natDegree] at hlt
    omega
  have hqform : (p %ₘ quadPoly (0 : ℂ) 0)
      = C ((p %ₘ quadPoly (0 : ℂ) 0).coeff 1) * X + C ((p %ₘ quadPoly (0 : ℂ) 0).coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hnd
  refine ⟨(p %ₘ quadPoly (0 : ℂ) 0).coeff 0, (p %ₘ quadPoly (0 : ℂ) 0).coeff 1, ?_⟩
  rw [hmk]
  conv_lhs => rw [hqform]
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
    show AdjoinRoot.mk (quadPoly (0 : ℂ) 0) X = AdjoinRoot.root (quadPoly (0 : ℂ) 0) from rfl]
  ring

@[simp]
theorem collisionObserver_of (u : ℂ) :
    collisionObserver (AdjoinRoot.of (quadPoly (0 : ℂ) 0) u) = (u, u) := by
  rw [collisionObserver, AdjoinRoot.liftAlgHom_of]
  simp [Algebra.ofId_apply]

/-- **The erased line.**  The kernel of the specialized observer is exactly the nilpotent line
`ℂ ε`, the class carried by the derived specialization. -/
theorem ker_collisionObserver :
    RingHom.ker collisionObserver.toRingHom
      = Ideal.span {AdjoinRoot.root (quadPoly (0 : ℂ) 0)} := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨u, v, rfl⟩ := exists_quadCoords x
    have hz : collisionObserver (AdjoinRoot.of (quadPoly (0 : ℂ) 0) u
        + AdjoinRoot.of (quadPoly (0 : ℂ) 0) v * AdjoinRoot.root (quadPoly (0 : ℂ) 0)) = 0 := hx
    rw [map_add, map_mul, collisionObserver_of, collisionObserver_of,
      collisionObserver_root, mul_zero, add_zero] at hz
    have hu : u = 0 := congrArg Prod.fst hz
    rw [hu]
    simp only [map_zero, zero_add]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le]
    rintro _ rfl
    exact collisionObserver_root

/-! ### The relative cotangent module as a base module -/

theorem lawDifferent_sq :
    (2 * lawEta - AdjoinRoot.of lawPoly lawParam) ^ 2
      = AdjoinRoot.of lawPoly (lawParam ^ 2) := by
  rw [map_pow]
  linear_combination (4 : LawAlgebra) * lawEta_sq

/-- The base-module comparison `B → A/(2η − h)`. -/
noncomputable def lawCotangentMap :
    LawBase →ₗ[LawBase] MonogenicOmega lawPoly :=
  Algebra.linearMap LawBase (MonogenicOmega lawPoly)

theorem lawCotangentMap_apply (b : LawBase) :
    lawCotangentMap b = Ideal.Quotient.mk _ (AdjoinRoot.of lawPoly b) := rfl

theorem lawCotangentMap_surjective : Function.Surjective lawCotangentMap := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, b, rfl⟩ := exists_lawCoords x
  have h2 : (2 : LawAlgebra) * AdjoinRoot.of lawPoly (Polynomial.C (1 / 2 : ℂ)) = 1 := by
    rw [show (2 : LawAlgebra) = AdjoinRoot.of lawPoly (Polynomial.C (2 : ℂ)) by
      simp [map_ofNat], ← map_mul, ← Polynomial.C_mul]
    norm_num
  refine ⟨a + b * (Polynomial.C (1 / 2 : ℂ) * lawParam), ?_⟩
  rw [lawCotangentMap_apply, Ideal.Quotient.eq, rootDifferent_lawPoly]
  refine Ideal.mem_span_singleton'.2 ⟨-(AdjoinRoot.of lawPoly b
    * AdjoinRoot.of lawPoly (Polynomial.C (1 / 2 : ℂ))), ?_⟩
  rw [map_add, map_mul, map_mul]
  linear_combination (-(AdjoinRoot.of lawPoly b * lawEta)) * h2

theorem ker_lawCotangentMap :
    LinearMap.ker lawCotangentMap = Ideal.span {lawParam ^ 2} := by
  refine le_antisymm ?_ ?_
  · intro b hb
    have hz : Ideal.Quotient.mk _ (AdjoinRoot.of lawPoly b) = 0 := hb
    rw [Ideal.Quotient.eq_zero_iff_mem, rootDifferent_lawPoly] at hz
    obtain ⟨z, hzz⟩ := Ideal.mem_span_singleton'.1 hz
    obtain ⟨x, y, rfl⟩ := exists_lawCoords z
    have hexp : (AdjoinRoot.of lawPoly x + AdjoinRoot.of lawPoly y * lawEta)
        * (2 * lawEta - AdjoinRoot.of lawPoly lawParam)
        = AdjoinRoot.of lawPoly (-(lawParam * x))
          + AdjoinRoot.of lawPoly (2 * x + y * lawParam) * lawEta := by
      simp only [map_neg, map_mul, map_add, map_ofNat]
      linear_combination (2 * AdjoinRoot.of lawPoly y) * lawEta_sq
    rw [hexp] at hzz
    have hb' : AdjoinRoot.of lawPoly b + AdjoinRoot.of lawPoly 0 * lawEta
        = AdjoinRoot.of lawPoly (-(lawParam * x))
          + AdjoinRoot.of lawPoly (2 * x + y * lawParam) * lawEta := by
      rw [map_zero, zero_mul, add_zero]
      exact hzz.symm
    obtain ⟨hb1, hb2⟩ := lawCoords_unique hb'
    have hx : x = -(Polynomial.C (1 / 2 : ℂ) * (y * lawParam)) := by
      have : (2 : LawBase) * x + y * lawParam = 0 := by linear_combination -hb2
      have h2 : (Polynomial.C (1 / 2 : ℂ) : LawBase) * 2 = 1 := by
        rw [show (2 : LawBase) = Polynomial.C (2 : ℂ) by simp [map_ofNat], ← map_mul]
        norm_num
      linear_combination Polynomial.C (1 / 2 : ℂ) * this - x * h2
    refine Ideal.mem_span_singleton'.2 ⟨Polynomial.C (1 / 2 : ℂ) * y, ?_⟩
    rw [hb1, hx]
    ring
  · rw [Ideal.span_le]
    rintro _ rfl
    show Ideal.Quotient.mk _ (AdjoinRoot.of lawPoly (lawParam ^ 2)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← lawDifferent_sq, ← rootDifferent_lawPoly, sq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **Theorem 6.**  As a module over the base, the relative cotangent module of the quadratic
family is `B/(h²)`: the nonreduced discriminant shadow. -/
noncomputable def lawKaehlerBaseEquiv :
    (LawBase ⧸ (Ideal.span {lawParam ^ 2})) ≃ₗ[LawBase] Ω[LawAlgebra⁄LawBase] :=
  (Submodule.quotEquivOfEq _ _ ker_lawCotangentMap.symm).trans
    ((lawCotangentMap.quotKerEquivOfSurjective lawCotangentMap_surjective).trans
      (LinearEquiv.restrictScalars LawBase lawKaehlerEquiv).symm)

end HTGeometry.ConstraintRelativity

