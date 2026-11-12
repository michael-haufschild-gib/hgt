import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros

/-!
# The index of a virtual configuration counts its zeros and its poles

A quotient of `L`-functions has zeros and poles. On the side of the zeros it is a difference of
two zero configurations `A` and `B`, with the net multiplicity `m_A(ρ) − m_B(ρ)` at each point
(`extMult`), and its Weil form is the difference `W_A − W_B`. For tempered `A`, `B`:

  the largest number of negative squares of `W_A − W_B` on a finite family of tests is the
  number of points right of the critical line with net multiplicity `≠ 0`, plus the number of
  points on the line with net multiplicity `< 0`

(`exists_le_negIndex_sub_zeroGram_iff`, in `ℕ∞`). Right of the line a zero and a pole count
alike: the pair `ρ, 1 − ρ̄` is a hyperbolic plane whatever the sign. On the line a zero is a
positive square and a pole a negative one. So `W_A − W_B` has no negative square on any family
iff the quotient has neither zero nor pole off the line and no pole on it
(`forall_negIndex_sub_zeroGram_eq_zero_iff`).

This is the index law for a virtual character: by Brauer's theorem (not in the corpus) the
`L`-function of an Artin character is a quotient of products of Hecke `L`-functions, and its
form is the difference of the forms of the two products.

* **Upper bound** (`negIndex_sub_zeroGram_le`). On the tests whose transforms vanish at the
  zeros of `P` and `N` right of the line and at the zeros of `N` on the line, every summand of
  `W_N` vanishes and `W_P` is a sum of squares.
* **Attainment** (`exists_sub_zeroGram_negIndex_ge`), for disjoint `P`, `N`. In the zero-side
  coordinates of the union, `W_P − W_N = ⟨T X(g), X(f)⟩` with the twisted reflection
  `(T x)_τ = s_τ x_{1−τ̄}`, `s = ±1` on `P`, `N` (`sub_W_eq_inner`). The vectors
  `e_ρ − s_ρ e_{1−ρ̄}` have `⟨T w, w⟩ = −2` off the line and `−4` at a zero of `N` on the line,
  and are orthogonal for `T`; the coordinates of tests are dense.
* **Cancellation** (`netPart`, `sub_W_eq_netPart`). `W_A − W_B = W_P − W_N` with `P`, `N` the
  positive and negative parts of the net multiplicity; they are disjoint and tempered.
-/

open Complex Matrix Finset
open scoped ComplexConjugate lp
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCastelnuovoSeveri

/-! ### The defect set of a pair and the upper bound -/

/-- The zeros of a configuration on the critical line. -/
def lineZeros (Z : ZeroConfig) : Set ℂ := {ρ ∈ Z.carrier | ρ.re = 1 / 2}

/-- The points that carry a negative square of `W_P − W_N`: the zeros of `P` and of `N` right of
the line and the zeros of `N` on the line. -/
def pairDefect (P N : ZeroConfig) : Set ℂ := rightZeros P ∪ rightZeros N ∪ lineZeros N

theorem hermQuad_sub {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (x : ι → ℂ) :
    hermQuad (A - B) x = hermQuad A x - hermQuad B x := by
  simp only [hermQuad, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

/-- **Upper bound.** `W_P − W_N` has at most as many negative squares as the pair has defect
points. -/
theorem negIndex_sub_zeroGram_le (P N : ZeroConfig) (hP : TemperedConfig P)
    (hN : TemperedConfig N) {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (zeroGram P f - zeroGram N f) : ℕ∞) ≤ (pairDefect P N).encard := by
  rcases (pairDefect P N).finite_or_infinite with hR | hR
  · haveI := hR.fintype
    rw [hR.encard_eq_coe_toFinset_card, Set.Finite.card_toFinset]
    refine ENat.coe_le_coe.mpr (negIndex_le_card_of_nonneg_on_ker _
      (fun ρ : pairDefect P N => evalFunctional f (gammaOf ρ)) fun x hx => ?_)
    have hvan : ∀ ρ ∈ pairDefect P N, paperFT (∑ i, conj (x i) • f i) (gammaOf ρ) = 0 := by
      intro ρ hρ
      have := hx ⟨ρ, hρ⟩
      rw [evalFunctional_eq f (fun i => (hf i).continuous) hfc] at this
      simpa using this
    have hFd := contDiff_sum_smul f hf fun i => conj (x i)
    have hFc := hasCompactSupport_sum_smul f hfc fun i => conj (x i)
    have h1 : 0 ≤ (P.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i)).re := by
      rw [ZeroConfig.W, Complex.re_tsum (summable_Wsummand P hP hFd hFc hFd hFc)]
      exact tsum_nonneg fun ρ => re_Wsummand_nonneg P
        (fun ρ hρ hre => hvan ρ (Or.inl (Or.inl ⟨hρ, hre⟩))) ρ
    -- every summand of `W_N` vanishes
    have hz : ∀ τ : N.carrier,
        N.Wsummand (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i) τ = 0 := by
      rintro ⟨ρ, hρ⟩
      simp only [ZeroConfig.Wsummand]
      rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
      · have hre : 1 / 2 < (reflect ρ).re := by
          simp [reflect]
          linarith
        have h0 := hvan _ (Or.inl (Or.inr ⟨N.reflect_mem ρ hρ, hre⟩))
        rw [gammaOf_reflect] at h0
        rw [h0, map_zero, mul_zero]
      · rw [hvan ρ (Or.inr ⟨hρ, heq⟩), mul_zero, zero_mul]
      · rw [hvan ρ (Or.inl (Or.inr ⟨hρ, hgt⟩)), mul_zero, zero_mul]
    have h2 : N.W (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i) = 0 := by
      rw [ZeroConfig.W, tsum_congr hz, tsum_zero]
    rw [hermQuad_sub, hermQuad_zeroGram_of_tempered P hP f hf hfc,
      hermQuad_zeroGram_of_tempered N hN f hf hfc, h2, Complex.zero_re, sub_zero]
    exact h1
  · rw [hR.encard_eq]
    exact le_top

/-! ### The union of two configurations and the twisted reflection -/

section Pair

variable (P N : ZeroConfig)

open Classical in
/-- The union of two configurations; on a common zero it has the multiplicity of the first. -/
def pairUnion : ZeroConfig where
  carrier := P.carrier ∪ N.carrier
  mult := fun ρ => if ρ ∈ P.carrier then P.mult ρ else N.mult ρ
  one_le_mult := by
    intro ρ hρ
    show 1 ≤ if ρ ∈ P.carrier then P.mult ρ else N.mult ρ
    by_cases h : ρ ∈ P.carrier
    · rw [if_pos h]
      exact P.one_le_mult ρ h
    · rw [if_neg h]
      exact N.one_le_mult ρ (hρ.resolve_left h)
  strip := fun ρ hρ => hρ.elim (P.strip ρ) (N.strip ρ)
  reflect_mem := fun ρ hρ =>
    hρ.elim (fun h => Or.inl (P.reflect_mem ρ h)) (fun h => Or.inr (N.reflect_mem ρ h))
  mult_reflect := by
    intro ρ hρ
    show (if reflect ρ ∈ P.carrier then P.mult (reflect ρ) else N.mult (reflect ρ)) =
      if ρ ∈ P.carrier then P.mult ρ else N.mult ρ
    have hrr : reflect (reflect ρ) = ρ := by simp [reflect]
    by_cases h : ρ ∈ P.carrier
    · rw [if_pos (P.reflect_mem ρ h), if_pos h, P.mult_reflect ρ h]
    · have h' : reflect ρ ∉ P.carrier := fun h' => h (hrr ▸ P.reflect_mem _ h')
      rw [if_neg h', if_neg h, N.mult_reflect ρ (hρ.resolve_left h)]
  finite_window := fun T₁ T₂ => by
    refine ((P.finite_window T₁ T₂).union (N.finite_window T₁ T₂)).subset ?_
    rintro ρ ⟨h1 | h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

theorem temperedConfig_pairUnion (hP : TemperedConfig P) (hN : TemperedConfig N)
    (hd : Disjoint P.carrier N.carrier) : TemperedConfig (pairUnion P N) := by
  classical
  have h1 := (summable_subtype_iff_indicator
    (f := fun ρ : ℂ => (P.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))).mp hP
  have h2 := (summable_subtype_iff_indicator
    (f := fun ρ : ℂ => (N.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))).mp hN
  refine (summable_subtype_iff_indicator
    (f := fun ρ : ℂ => ((pairUnion P N).mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))).mpr
    ((h1.add h2).congr fun ρ => ?_)
  by_cases hp : ρ ∈ P.carrier
  · have hn : ρ ∉ N.carrier := Set.disjoint_left.mp hd hp
    rw [Set.indicator_of_mem (show ρ ∈ (pairUnion P N).carrier from Or.inl hp),
      Set.indicator_of_mem hp, Set.indicator_of_notMem hn, add_zero,
      show (pairUnion P N).mult ρ = P.mult ρ from if_pos hp]
  · by_cases hn : ρ ∈ N.carrier
    · rw [Set.indicator_of_mem (show ρ ∈ (pairUnion P N).carrier from Or.inr hn),
        Set.indicator_of_notMem hp, Set.indicator_of_mem hn, zero_add,
        show (pairUnion P N).mult ρ = N.mult ρ from if_neg hp]
    · rw [Set.indicator_of_notMem (show ρ ∉ (pairUnion P N).carrier from fun h => h.elim hp hn),
        Set.indicator_of_notMem hp, Set.indicator_of_notMem hn, add_zero]

open Classical in
/-- The sign of a point: `+1` on the zeros of `P`, `−1` elsewhere. -/
def signOf (ρ : ℂ) : ℂ := if ρ ∈ P.carrier then 1 else -1

theorem signOf_mul_self (ρ : ℂ) : signOf P ρ * signOf P ρ = 1 := by
  unfold signOf
  split_ifs <;> norm_num

theorem norm_signOf (ρ : ℂ) : ‖signOf P ρ‖ = 1 := by
  unfold signOf
  split_ifs <;> simp

theorem conj_signOf (ρ : ℂ) : conj (signOf P ρ) = signOf P ρ := by
  unfold signOf
  split_ifs <;> simp

theorem signOf_reflect (ρ : ℂ) : signOf P (reflect ρ) = signOf P ρ := by
  have hrr : reflect (reflect ρ) = ρ := by simp [reflect]
  unfold signOf
  by_cases h : ρ ∈ P.carrier
  · rw [if_pos (P.reflect_mem ρ h), if_pos h]
  · rw [if_neg fun h' => h (hrr ▸ P.reflect_mem _ h'), if_neg h]

theorem signOf_reflectCarrier (a : (pairUnion P N).carrier) :
    signOf P (reflectCarrier (pairUnion P N) a : (pairUnion P N).carrier) = signOf P a :=
  signOf_reflect P a

/-- The twisted reflection of the coordinates on the union: `(T x)_τ = s_τ x_{1−τ̄}`. -/
def twist (x : ℓ²((pairUnion P N).carrier, ℂ)) : ℓ²((pairUnion P N).carrier, ℂ) :=
  ⟨fun τ => signOf P τ * x (reflectCarrier (pairUnion P N) τ), by
    refine (memℓp_gen_iff (by norm_num)).mpr ?_
    refine ((memℓp_gen_iff (by norm_num)).mp (memℓp_reflect (pairUnion P N) x)).congr fun τ => ?_
    rw [norm_mul, norm_signOf, one_mul]⟩

theorem twist_apply (x : ℓ²((pairUnion P N).carrier, ℂ)) (τ : (pairUnion P N).carrier) :
    twist P N x τ = signOf P τ * x (reflectCarrier (pairUnion P N) τ) := rfl

theorem twist_add (x y : ℓ²((pairUnion P N).carrier, ℂ)) :
    twist P N (x + y) = twist P N x + twist P N y := by
  ext τ
  simp only [twist_apply, lp.coeFn_add, Pi.add_apply, mul_add]

theorem twist_sub (x y : ℓ²((pairUnion P N).carrier, ℂ)) :
    twist P N (x - y) = twist P N x - twist P N y := by
  ext τ
  simp only [twist_apply, lp.coeFn_sub, Pi.sub_apply, mul_sub]

theorem twist_smul (c : ℂ) (x : ℓ²((pairUnion P N).carrier, ℂ)) :
    twist P N (c • x) = c • twist P N x := by
  ext τ
  simp only [twist_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_twist (x : ℓ²((pairUnion P N).carrier, ℂ)) : ‖twist P N x‖ = ‖x‖ := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have h := lp.norm_rpow_eq_tsum h2 (twist P N x)
  have hx := lp.norm_rpow_eq_tsum h2 x
  simp only [twist_apply, norm_mul, norm_signOf, one_mul] at h
  have ht := (reflectEquiv (pairUnion P N)).tsum_eq (fun τ => ‖x τ‖ ^ (2 : ENNReal).toReal)
  simp only [reflectEquiv_apply] at ht
  rw [ht, ← hx] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← Real.sqrt_sq (norm_nonneg (twist P N x)), h, Real.sqrt_sq (norm_nonneg x)]

theorem twist_single [DecidableEq (pairUnion P N).carrier] (a : (pairUnion P N).carrier) :
    twist P N (lp.single 2 a (1 : ℂ)) =
      signOf P a • lp.single 2 (reflectCarrier (pairUnion P N) a) (1 : ℂ) := by
  ext τ
  simp only [twist_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply,
    Pi.single_apply]
  by_cases h : τ = reflectCarrier (pairUnion P N) a
  · subst h
    rw [reflectCarrier_reflectCarrier, if_pos rfl, if_pos rfl, signOf_reflectCarrier]
  · have h' : reflectCarrier (pairUnion P N) τ ≠ a := fun h'' =>
      h (by rw [← h'', reflectCarrier_reflectCarrier])
    rw [if_neg h', if_neg h, mul_zero, mul_zero]

/-- **The difference of two Weil forms is a Krein form** on the coordinates of the union:
`W_P(f, g) − W_N(f, g) = ⟨T X(g), X(f)⟩`. -/
theorem sub_W_eq_inner (hP : TemperedConfig P) (hN : TemperedConfig N)
    (hd : Disjoint P.carrier N.carrier) (hS : TemperedConfig (pairUnion P N))
    (f g : testSpace) :
    P.W f g - N.W f g =
      inner ℂ (twist P N (zeroMap (pairUnion P N) hS g)) (zeroMap (pairUnion P N) hS f) := by
  classical
  have hterm : ∀ τ : (pairUnion P N).carrier,
      inner ℂ (twist P N (zeroMap (pairUnion P N) hS g) τ) (zeroMap (pairUnion P N) hS f τ) =
        signOf P τ * (pairUnion P N).Wsummand f g τ := by
    intro τ
    have hm : (pairUnion P N).mult (reflect (τ : ℂ)) = (pairUnion P N).mult τ :=
      (pairUnion P N).mult_reflect _ τ.2
    have hsq : ((Real.sqrt ((pairUnion P N).mult τ) : ℝ) : ℂ) *
        (Real.sqrt ((pairUnion P N).mult τ) : ℝ) = ((pairUnion P N).mult τ : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    simp only [RCLike.inner_apply', twist_apply, zeroMap_apply, zeroCoord, reflectCarrier, hm,
      gammaOf_reflect, map_mul, Complex.conj_ofReal, conj_signOf, ZeroConfig.Wsummand]
    linear_combination (signOf P (τ : ℂ) * paperFT (f : ℝ → ℂ) (gammaOf (τ : ℂ)) *
      (starRingEnd ℂ) (paperFT (g : ℝ → ℂ) ((starRingEnd ℂ) (gammaOf (τ : ℂ))))) * hsq
  have hPs : HasSum (P.carrier.indicator (P.Wsummand f g)) (P.W f g) :=
    (hasSum_subtype_iff_indicator (f := P.Wsummand f g)).mp
      (summable_Wsummand P hP f.2.1 f.2.2 g.2.1 g.2.2).hasSum
  have hNs : HasSum (N.carrier.indicator (N.Wsummand f g)) (N.W f g) :=
    (hasSum_subtype_iff_indicator (f := N.Wsummand f g)).mp
      (summable_Wsummand N hN f.2.1 f.2.2 g.2.1 g.2.2).hasSum
  have hfun : ((pairUnion P N).carrier.indicator
      fun ρ => signOf P ρ * (pairUnion P N).Wsummand f g ρ) =
        fun ρ => P.carrier.indicator (P.Wsummand f g) ρ -
          N.carrier.indicator (N.Wsummand f g) ρ := by
    funext ρ
    by_cases hp : ρ ∈ P.carrier
    · have hn : ρ ∉ N.carrier := Set.disjoint_left.mp hd hp
      rw [Set.indicator_of_mem (show ρ ∈ (pairUnion P N).carrier from Or.inl hp),
        Set.indicator_of_mem hp, Set.indicator_of_notMem hn, sub_zero, signOf, if_pos hp,
        one_mul, ZeroConfig.Wsummand, ZeroConfig.Wsummand,
        show (pairUnion P N).mult ρ = P.mult ρ from if_pos hp]
    · by_cases hn : ρ ∈ N.carrier
      · rw [Set.indicator_of_mem (show ρ ∈ (pairUnion P N).carrier from Or.inr hn),
          Set.indicator_of_notMem hp, Set.indicator_of_mem hn, zero_sub, signOf, if_neg hp,
          ZeroConfig.Wsummand, ZeroConfig.Wsummand,
          show (pairUnion P N).mult ρ = N.mult ρ from if_neg hp]
        ring
      · rw [Set.indicator_of_notMem
            (show ρ ∉ (pairUnion P N).carrier from fun h => h.elim hp hn),
          Set.indicator_of_notMem hp, Set.indicator_of_notMem hn, sub_zero]
  have hSs : HasSum ((pairUnion P N).carrier.indicator
      fun ρ => signOf P ρ * (pairUnion P N).Wsummand f g ρ) (P.W f g - N.W f g) := by
    rw [hfun]
    exact hPs.sub hNs
  rw [lp.inner_eq_tsum, tsum_congr hterm]
  exact ((hasSum_subtype_iff_indicator
    (f := fun ρ => signOf P ρ * (pairUnion P N).Wsummand f g ρ)).mpr hSs).tsum_eq.symm

/-! ### Attainment -/

/-- A Gram matrix within `η` of a diagonal matrix with entries `≤ −2`, with `η · n ≤ 1`, has
form `≤ −|x|²`. -/
theorem hermQuad_le_of_near_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (d : ι → ℝ) (hd : ∀ i, d i ≤ -2) {η : ℝ} (hη : η * Fintype.card ι ≤ 1)
    (hG : ∀ i j, ‖G i j - (if i = j then (d i : ℂ) else 0)‖ ≤ η) (x : ι → ℂ) :
    hermQuad G x ≤ -∑ i, ‖x i‖ ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [hermQuad, dotProduct]
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hG i₀ i₀)
  set D : Matrix ι ι ℂ := diagonal fun i => ((d i : ℝ) : ℂ) with hD
  set E : Matrix ι ι ℂ := G - D with hE
  have hsplit : hermQuad G x = hermQuad D x + hermQuad E x := by
    have hGDE : G = D + E := by rw [hE]; abel
    rw [hGDE]
    simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  have hDx : hermQuad D x ≤ -2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [hD, hermQuad_diagonal, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]
    exact mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _)
  have hEij : ∀ i j, ‖E i j‖ ≤ η := fun i j => by
    have hDij : D i j = if i = j then (d i : ℂ) else 0 := by
      simp only [hD, Matrix.diagonal_apply]
    rw [hE, Matrix.sub_apply, hDij]
    exact hG i j
  have hEx : hermQuad E x ≤ η * (∑ i, ‖x i‖) ^ 2 := by
    calc hermQuad E x ≤ ‖star x ⬝ᵥ E *ᵥ x‖ := Complex.re_le_norm _
      _ ≤ ∑ i, ‖x i‖ * ∑ j, ‖E i j‖ * ‖x j‖ := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)) (norm_nonneg _)
      _ ≤ ∑ i, ‖x i‖ * ∑ j, η * ‖x j‖ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_right (hEij i j) (norm_nonneg _)) (norm_nonneg _)
      _ = η * (∑ i, ‖x i‖) ^ 2 := by
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        ring
  have hcs : (∑ i, ‖x i‖) ^ 2 ≤ Fintype.card ι * ∑ i, ‖x i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ‖x i‖)
    simpa [Finset.card_univ] using this
  have hX : 0 ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : η * (∑ i, ‖x i‖) ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
    calc η * (∑ i, ‖x i‖) ^ 2 ≤ η * (Fintype.card ι * ∑ i, ‖x i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hη0
      _ = (η * Fintype.card ι) * ∑ i, ‖x i‖ ^ 2 := by ring
      _ ≤ 1 * ∑ i, ‖x i‖ ^ 2 := mul_le_mul_of_nonneg_right hη hX
      _ = ∑ i, ‖x i‖ ^ 2 := one_mul _
  rw [hsplit]
  linarith

theorem reflect_eq_self {ρ : ℂ} (h : ρ.re = 1 / 2) : reflect ρ = ρ := by
  apply Complex.ext
  · simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp only [reflect, Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring

/-- **Attainment.** For finitely many distinct defect points of a disjoint pair there are tests
on which `W_P − W_N` has at least that many negative squares. -/
theorem exists_sub_zeroGram_negIndex_ge (hP : TemperedConfig P) (hN : TemperedConfig N)
    (hd : Disjoint P.carrier N.carrier) {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : ι → ℂ)
    (hρ : Function.Injective ρ) (hR : ∀ i, ρ i ∈ pairDefect P N) :
    ∃ f : ι → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      Fintype.card ι ≤ hermNegIndex (zeroGram P f - zeroGram N f) := by
  classical
  have hS := temperedConfig_pairUnion P N hP hN hd
  have hmem : ∀ i, ρ i ∈ (pairUnion P N).carrier := fun i => by
    rcases hR i with (h | h) | h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact Or.inr h.1
  have hre : ∀ i, 1 / 2 ≤ (ρ i).re := fun i => by
    rcases hR i with (h | h) | h
    · exact h.2.le
    · exact h.2.le
    · exact h.2.ge
  set r : ι → (pairUnion P N).carrier := fun i => ⟨ρ i, hmem i⟩ with hr
  -- a defect point fixed by the reflection is a zero of `N` on the line
  have hfix : ∀ i, reflectCarrier (pairUnion P N) (r i) = r i → signOf P (ρ i) = -1 := by
    intro i h
    have hv : reflect (ρ i) = ρ i := congrArg Subtype.val h
    have h1 := congrArg Complex.re hv
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at h1
    rcases hR i with (h' | h') | h'
    · linarith [h'.2]
    · linarith [h'.2]
    · rw [signOf, if_neg (Set.disjoint_right.mp hd h'.1)]
  have hne : ∀ i j, i ≠ j → reflectCarrier (pairUnion P N) (r j) ≠ r i := by
    intro i j hij h
    have hv : reflect (ρ j) = ρ i := congrArg Subtype.val h
    have h1 := congrArg Complex.re hv
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at h1
    have hj : (ρ j).re = 1 / 2 := by linarith [hre i, hre j]
    rw [reflect_eq_self hj] at hv
    exact hij (hρ hv).symm
  have hrr : ∀ i j, r j = r i ↔ i = j := fun i j =>
    ⟨fun h => (hρ (congrArg Subtype.val h)).symm, fun h => h ▸ rfl⟩
  have hRr : ∀ i j, reflectCarrier (pairUnion P N) (r j) = reflectCarrier (pairUnion P N) (r i) ↔
      i = j := fun i j =>
    ⟨fun h => (hrr i j).mp ((reflectEquiv (pairUnion P N)).injective h), fun h => h ▸ rfl⟩
  -- the negative vectors `e_ρ − s_ρ e_{1−ρ̄}` of the Krein form
  set w : ι → ℓ²((pairUnion P N).carrier, ℂ) := fun i =>
    lp.single 2 (r i) (1 : ℂ) -
      signOf P (ρ i) • lp.single 2 (reflectCarrier (pairUnion P N) (r i)) (1 : ℂ) with hw
  set d : ι → ℝ := fun i => if reflectCarrier (pairUnion P N) (r i) = r i then -4 else -2
    with hdd
  have hd2 : ∀ i, d i ≤ -2 := fun i => by
    simp only [hdd]
    split_ifs <;> norm_num
  have htw : ∀ j, twist P N (w j) =
      signOf P (ρ j) • lp.single 2 (reflectCarrier (pairUnion P N) (r j)) (1 : ℂ) -
        lp.single 2 (r j) (1 : ℂ) := by
    intro j
    have hs1 : signOf P ((r j : (pairUnion P N).carrier) : ℂ) = signOf P (ρ j) := rfl
    have hs2 : signOf P ((reflectCarrier (pairUnion P N) (r j) : (pairUnion P N).carrier) : ℂ) =
        signOf P (ρ j) := signOf_reflectCarrier P N (r j)
    simp only [hw]
    rw [twist_sub, twist_smul, twist_single, twist_single, reflectCarrier_reflectCarrier,
      smul_smul, hs1, hs2, signOf_mul_self, one_smul]
  have hRw : ∀ i j, inner ℂ (twist P N (w j)) (w i) = if i = j then ((d i : ℝ) : ℂ) else 0 := by
    intro i j
    rw [htw j]
    simp only [hw, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_single_single, conj_signOf]
    by_cases hij : i = j
    · subst hij
      by_cases hfx : reflectCarrier (pairUnion P N) (r i) = r i
      · simp [hdd, hfx, hfix i hfx]
        norm_num
      · have hfx' : ¬ r i = reflectCarrier (pairUnion P N) (r i) := fun h => hfx h.symm
        simp [hdd, hfx, hfx', signOf_mul_self]
        norm_num
    · have h1 : ¬ r j = r i := fun h => hij ((hrr i j).mp h)
      have h2 : ¬ reflectCarrier (pairUnion P N) (r j) = reflectCarrier (pairUnion P N) (r i) :=
        fun h => hij ((hRr i j).mp h)
      have h3 : ¬ reflectCarrier (pairUnion P N) (r j) = r i := hne i j hij
      have h4 : ¬ r j = reflectCarrier (pairUnion P N) (r i) := fun h =>
        hne j i (Ne.symm hij) h.symm
      simp [hij, h1, h2, h3, h4]
  have hnw : ∀ i, ‖w i‖ ≤ 2 := fun i => by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_signOf, one_mul, lp.norm_single (by norm_num),
      lp.norm_single (by norm_num), norm_one]
    norm_num
  -- approximants of the negative vectors
  set k := Fintype.card ι with hk
  set ε : ℝ := 1 / (5 * ((k : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  choose g hg using fun i => exists_zeroMap_near (pairUnion P N) hS (w i) hε0
  refine ⟨fun i => (g i : ℝ → ℂ), fun i => (g i).2.1, fun i => (g i).2.2, ?_⟩
  have hentry : ∀ i j,
      ‖(zeroGram P (fun i => (g i : ℝ → ℂ)) - zeroGram N (fun i => (g i : ℝ → ℂ))) i j -
        (if i = j then ((d i : ℝ) : ℂ) else 0)‖ ≤ 5 * ε := by
    intro i j
    have hGij : (zeroGram P (fun i => (g i : ℝ → ℂ)) - zeroGram N (fun i => (g i : ℝ → ℂ))) i j =
        inner ℂ (twist P N (zeroMap (pairUnion P N) hS (g j)))
          (zeroMap (pairUnion P N) hS (g i)) :=
      sub_W_eq_inner P N hP hN hd hS (g i) (g j)
    have hdi : zeroMap (pairUnion P N) hS (g i) =
        w i + (zeroMap (pairUnion P N) hS (g i) - w i) := by abel
    have hdj : zeroMap (pairUnion P N) hS (g j) =
        w j + (zeroMap (pairUnion P N) hS (g j) - w j) := by abel
    set ei := zeroMap (pairUnion P N) hS (g i) - w i
    set ej := zeroMap (pairUnion P N) hS (g j) - w j
    have hei : ‖ei‖ < ε := hg i
    have hej : ‖ej‖ < ε := hg j
    rw [hGij, hdi, hdj, twist_add, inner_add_left, inner_add_right, inner_add_right, hRw i j]
    have h1 := (norm_inner_le_norm (𝕜 := ℂ) (twist P N (w j)) ei).trans_eq
      (by rw [norm_twist])
    have h2 := (norm_inner_le_norm (𝕜 := ℂ) (twist P N ej) (w i)).trans_eq
      (by rw [norm_twist])
    have h3 := (norm_inner_le_norm (𝕜 := ℂ) (twist P N ej) ei).trans_eq
      (by rw [norm_twist])
    calc ‖(if i = j then ((d i : ℝ) : ℂ) else 0) + inner ℂ (twist P N (w j)) ei +
          (inner ℂ (twist P N ej) (w i) + inner ℂ (twist P N ej) ei) -
            (if i = j then ((d i : ℝ) : ℂ) else 0)‖
        = ‖inner ℂ (twist P N (w j)) ei + inner ℂ (twist P N ej) (w i) +
            inner ℂ (twist P N ej) ei‖ := by congr 1; ring
      _ ≤ ‖w j‖ * ‖ei‖ + ‖ej‖ * ‖w i‖ + ‖ej‖ * ‖ei‖ :=
        norm_add₃_le.trans (add_le_add (add_le_add h1 h2) h3)
      _ ≤ 2 * ε + ε * 2 + ε * ε := by
        have := hnw i; have := hnw j
        gcongr
      _ ≤ 5 * ε := by nlinarith
  have hη : 5 * ε * (Fintype.card ι : ℝ) ≤ 1 := by
    rw [← hk, hε]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    rw [show 5 * (1 / (5 * ((k : ℝ) + 1))) * k = k / (k + 1) by field_simp,
      div_le_one (by positivity)]
    linarith
  have hpd : IsPosDefOn
      (-(zeroGram P (fun i => (g i : ℝ → ℂ)) - zeroGram N fun i => (g i : ℝ → ℂ))) ⊤ :=
    fun x _ hx0 => by
      rw [hermQuad_neg]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
      have hpos : 0 < ∑ i, ‖x i‖ ^ 2 :=
        lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) (Finset.single_le_sum
          (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
      linarith [hermQuad_le_of_near_diag _ d hd2 hη hentry x]
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card] at h1
  rw [hermNegIndex]
  exact h1

end Pair

/-! ### Cancellation: the net multiplicity -/

open Classical in
/-- The multiplicity of a configuration at a point, zero off the carrier. -/
def extMult (Z : ZeroConfig) (ρ : ℂ) : ℕ := if ρ ∈ Z.carrier then Z.mult ρ else 0

theorem extMult_reflect (Z : ZeroConfig) (ρ : ℂ) : extMult Z (reflect ρ) = extMult Z ρ := by
  have hrr : reflect (reflect ρ) = ρ := by simp [reflect]
  unfold extMult
  by_cases h : ρ ∈ Z.carrier
  · rw [if_pos (Z.reflect_mem ρ h), if_pos h, Z.mult_reflect ρ h]
  · rw [if_neg fun h' => h (hrr ▸ Z.reflect_mem _ h'), if_neg h]

theorem mem_carrier_of_extMult_pos {Z : ZeroConfig} {ρ : ℂ} (h : 0 < extMult Z ρ) :
    ρ ∈ Z.carrier := by
  by_contra hn
  rw [extMult, if_neg hn] at h
  exact lt_irrefl _ h

/-- The positive part of `A − B`: the points where `A` has the larger multiplicity, with the
difference as multiplicity. -/
def netPart (A B : ZeroConfig) : ZeroConfig where
  carrier := {ρ | extMult B ρ < extMult A ρ}
  mult := fun ρ => extMult A ρ - extMult B ρ
  one_le_mult := fun ρ h => Nat.sub_pos_of_lt h
  strip := fun ρ h => A.strip ρ (mem_carrier_of_extMult_pos (lt_of_le_of_lt (Nat.zero_le _) h))
  reflect_mem := fun ρ h => by
    show extMult B (reflect ρ) < extMult A (reflect ρ)
    rw [extMult_reflect, extMult_reflect]
    exact h
  mult_reflect := fun ρ _ => by
    show extMult A (reflect ρ) - extMult B (reflect ρ) = extMult A ρ - extMult B ρ
    rw [extMult_reflect, extMult_reflect]
  finite_window := fun T₁ T₂ => (A.finite_window T₁ T₂).subset fun ρ h =>
    ⟨mem_carrier_of_extMult_pos (lt_of_le_of_lt (Nat.zero_le _) h.1), h.2⟩

theorem mem_netPart_carrier {A B : ZeroConfig} {ρ : ℂ} :
    ρ ∈ (netPart A B).carrier ↔ extMult B ρ < extMult A ρ := Iff.rfl

theorem disjoint_netPart (A B : ZeroConfig) :
    Disjoint (netPart A B).carrier (netPart B A).carrier :=
  Set.disjoint_left.mpr fun _ h1 h2 =>
    lt_asymm (mem_netPart_carrier.mp h1) (mem_netPart_carrier.mp h2)

theorem temperedConfig_netPart (A B : ZeroConfig) (hA : TemperedConfig A) :
    TemperedConfig (netPart A B) := by
  classical
  have h1 := (summable_subtype_iff_indicator
    (f := fun ρ : ℂ => (A.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))).mp hA
  have hpos : ∀ (m : ℕ) (ρ : ℂ), 0 ≤ (m : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := fun m ρ =>
    div_nonneg (Nat.cast_nonneg _) (by have := Complex.normSq_nonneg (gammaOf ρ); linarith)
  refine (summable_subtype_iff_indicator
    (f := fun ρ : ℂ => ((netPart A B).mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))).mpr
    (Summable.of_nonneg_of_le (fun ρ => Set.indicator_nonneg (fun ρ _ => hpos _ ρ) ρ)
      (fun ρ => ?_) h1)
  by_cases h : ρ ∈ (netPart A B).carrier
  · have hA' : ρ ∈ A.carrier :=
      mem_carrier_of_extMult_pos (lt_of_le_of_lt (Nat.zero_le _) (mem_netPart_carrier.mp h))
    have hle : ((netPart A B).mult ρ : ℝ) ≤ A.mult ρ := by
      have h2 : (netPart A B).mult ρ = extMult A ρ - extMult B ρ := rfl
      have h3 : extMult A ρ = A.mult ρ := if_pos hA'
      rw [h2, h3]
      exact_mod_cast Nat.sub_le _ _
    rw [Set.indicator_of_mem h, Set.indicator_of_mem hA']
    exact div_le_div_of_nonneg_right hle
      (by have := Complex.normSq_nonneg (gammaOf ρ); linarith)
  · rw [Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (fun ρ _ => hpos _ ρ) ρ

/-- The summand of Weil's form at a point, without the multiplicity. -/
def unitSummand (f g : ℝ → ℂ) (ρ : ℂ) : ℂ :=
  paperFT f (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ)))

theorem Wsummand_eq (Z : ZeroConfig) (f g : ℝ → ℂ) (ρ : ℂ) :
    Z.Wsummand f g ρ = (Z.mult ρ : ℂ) * unitSummand f g ρ := by
  rw [ZeroConfig.Wsummand, unitSummand, mul_assoc]

/-- **Cancellation.** The difference of two Weil forms is the difference of the forms of the
positive and the negative part of the net multiplicity. -/
theorem sub_W_eq_netPart (A B : ZeroConfig) (hA : TemperedConfig A) (hB : TemperedConfig B)
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    A.W f g - B.W f g = (netPart A B).W f g - (netPart B A).W f g := by
  classical
  have hW : ∀ Z : ZeroConfig, TemperedConfig Z →
      HasSum (Z.carrier.indicator (Z.Wsummand f g)) (Z.W f g) := fun Z hZ =>
    (hasSum_subtype_iff_indicator (f := Z.Wsummand f g)).mp
      (summable_Wsummand Z hZ hf hfc hg hgc).hasSum
  have hind : ∀ (Z : ZeroConfig) (ρ : ℂ),
      Z.carrier.indicator (Z.Wsummand f g) ρ = (extMult Z ρ : ℂ) * unitSummand f g ρ := by
    intro Z ρ
    by_cases h : ρ ∈ Z.carrier
    · rw [Set.indicator_of_mem h, extMult, if_pos h, Wsummand_eq]
    · rw [Set.indicator_of_notMem h, extMult, if_neg h, Nat.cast_zero, zero_mul]
  have hnet : ∀ (X Y : ZeroConfig) (ρ : ℂ),
      (netPart X Y).carrier.indicator ((netPart X Y).Wsummand f g) ρ =
        if extMult Y ρ < extMult X ρ then
          ((extMult X ρ : ℂ) - extMult Y ρ) * unitSummand f g ρ else 0 := by
    intro X Y ρ
    by_cases h : extMult Y ρ < extMult X ρ
    · rw [Set.indicator_of_mem (mem_netPart_carrier.mpr h), if_pos h, Wsummand_eq,
        show (netPart X Y).mult ρ = extMult X ρ - extMult Y ρ from rfl, Nat.cast_sub h.le]
    · rw [Set.indicator_of_notMem (fun h' => h (mem_netPart_carrier.mp h')), if_neg h]
  have hfun : (fun ρ => A.carrier.indicator (A.Wsummand f g) ρ -
      B.carrier.indicator (B.Wsummand f g) ρ) =
        fun ρ => (netPart A B).carrier.indicator ((netPart A B).Wsummand f g) ρ -
          (netPart B A).carrier.indicator ((netPart B A).Wsummand f g) ρ := by
    funext ρ
    rw [hind A ρ, hind B ρ, hnet A B ρ, hnet B A ρ]
    rcases lt_trichotomy (extMult A ρ) (extMult B ρ) with h | h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos h]
      ring
    · rw [if_neg (by omega), if_neg (by omega), h]
      ring
    · rw [if_pos h, if_neg (not_lt.mpr h.le)]
      ring
  have h1 : HasSum (fun ρ => (netPart A B).carrier.indicator ((netPart A B).Wsummand f g) ρ -
      (netPart B A).carrier.indicator ((netPart B A).Wsummand f g) ρ) (A.W f g - B.W f g) := by
    rw [← hfun]
    exact (hW A hA).sub (hW B hB)
  exact h1.unique
    ((hW _ (temperedConfig_netPart A B hA)).sub (hW _ (temperedConfig_netPart B A hB)))

theorem zeroGram_sub_eq_netPart (A B : ZeroConfig) (hA : TemperedConfig A)
    (hB : TemperedConfig B) {ι : Type*} (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    zeroGram A f - zeroGram B f = zeroGram (netPart A B) f - zeroGram (netPart B A) f := by
  ext i j
  simp only [Matrix.sub_apply, zeroGram]
  exact sub_W_eq_netPart A B hA hB (hf i) (hfc i) (hf j) (hfc j)

/-! ### The index law -/

/-- The defect set of a virtual configuration `A − B`: the points right of the line with net
multiplicity `≠ 0` and the points on the line with net multiplicity `< 0`. -/
def virtualDefect (A B : ZeroConfig) : Set ℂ :=
  {ρ | 1 / 2 < ρ.re ∧ extMult A ρ ≠ extMult B ρ} ∪ {ρ | ρ.re = 1 / 2 ∧ extMult A ρ < extMult B ρ}

theorem pairDefect_netPart (A B : ZeroConfig) :
    pairDefect (netPart A B) (netPart B A) = virtualDefect A B := by
  ext ρ
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl ⟨h.2, (ne_of_lt (mem_netPart_carrier.mp h.1)).symm⟩
    · exact Or.inl ⟨h.2, ne_of_lt (mem_netPart_carrier.mp h.1)⟩
    · exact Or.inr ⟨h.2, mem_netPart_carrier.mp h.1⟩
  · rintro (⟨hre, hne⟩ | ⟨hre, h⟩)
    · rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact Or.inl (Or.inr ⟨mem_netPart_carrier.mpr h, hre⟩)
      · exact Or.inl (Or.inl ⟨mem_netPart_carrier.mpr h, hre⟩)
    · exact Or.inr ⟨mem_netPart_carrier.mpr h, hre⟩

/-- **Upper bound for a virtual configuration.** -/
theorem negIndex_sub_zeroGram_le_virtualDefect (A B : ZeroConfig) (hA : TemperedConfig A)
    (hB : TemperedConfig B) {ι : Type*} [Fintype ι] (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (zeroGram A f - zeroGram B f) : ℕ∞) ≤ (virtualDefect A B).encard := by
  rw [zeroGram_sub_eq_netPart A B hA hB f hf hfc, ← pairDefect_netPart]
  exact negIndex_sub_zeroGram_le _ _ (temperedConfig_netPart A B hA)
    (temperedConfig_netPart B A hB) f hf hfc

/-- **The index law of a virtual configuration.** `W_A − W_B` has `n` negative squares on some
family of `n` tests iff `A − B` has at least `n` defect points: points right of the critical
line where the multiplicities differ, and points on the line where `B` has the larger one. -/
theorem exists_le_negIndex_sub_zeroGram_iff (A B : ZeroConfig) (hA : TemperedConfig A)
    (hB : TemperedConfig B) (n : ℕ) :
    (∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
        n ≤ hermNegIndex (zeroGram A f - zeroGram B f)) ↔
      (n : ℕ∞) ≤ (virtualDefect A B).encard := by
  classical
  constructor
  · rintro ⟨f, hf, hfc, hn⟩
    exact (ENat.coe_le_coe.mpr hn).trans
      (negIndex_sub_zeroGram_le_virtualDefect A B hA hB f hf hfc)
  · intro hn
    rw [← pairDefect_netPart] at hn
    obtain ⟨t, hts, htn⟩ := Set.exists_subset_encard_eq hn
    have htf : t.Finite := Set.finite_of_encard_eq_coe htn
    have hcard : htf.toFinset.card = n := by
      have h := htf.encard_eq_coe_toFinset_card
      rw [htn] at h
      exact_mod_cast h.symm
    set e := htf.toFinset.equivFin
    set ρ : Fin n → ℂ := fun i => (e.symm (Fin.cast hcard.symm i) : ℂ) with hρdef
    have hρ : Function.Injective ρ := fun i j h =>
      Fin.cast_injective _ (e.symm.injective (Subtype.ext h))
    have hR : ∀ i, ρ i ∈ pairDefect (netPart A B) (netPart B A) := fun i =>
      hts ((Set.Finite.mem_toFinset htf).mp (e.symm (Fin.cast hcard.symm i)).2)
    obtain ⟨f, hf, hfc, hge⟩ := exists_sub_zeroGram_negIndex_ge (netPart A B) (netPart B A)
      (temperedConfig_netPart A B hA) (temperedConfig_netPart B A hB) (disjoint_netPart A B)
      ρ hρ hR
    refine ⟨f, hf, hfc, ?_⟩
    rw [zeroGram_sub_eq_netPart A B hA hB f hf hfc]
    simpa using hge

/-- **Castelnuovo and Severi for a virtual configuration.** `W_A − W_B` has no negative square
on any family of tests iff right of the line the multiplicities agree and on the line `B` does
not exceed `A`: the quotient has neither zero nor pole off the line and no pole on it. -/
theorem forall_negIndex_sub_zeroGram_eq_zero_iff (A B : ZeroConfig) (hA : TemperedConfig A)
    (hB : TemperedConfig B) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
        (∀ i, HasCompactSupport (f i)) → hermNegIndex (zeroGram A f - zeroGram B f) = 0) ↔
      (∀ ρ : ℂ, 1 / 2 < ρ.re → extMult A ρ = extMult B ρ) ∧
        ∀ ρ : ℂ, ρ.re = 1 / 2 → extMult B ρ ≤ extMult A ρ := by
  constructor
  · intro h
    have hempty : ∀ ρ, ρ ∉ virtualDefect A B := by
      intro ρ hρ
      have h1 : ((1 : ℕ) : ℕ∞) ≤ (virtualDefect A B).encard := by
        rw [Nat.cast_one, Set.one_le_encard_iff_nonempty]
        exact ⟨ρ, hρ⟩
      obtain ⟨f, hf, hfc, hn⟩ := (exists_le_negIndex_sub_zeroGram_iff A B hA hB 1).mpr h1
      have := h 1 f hf hfc
      omega
    exact ⟨fun ρ hre => by_contra fun hne => hempty ρ (Or.inl ⟨hre, hne⟩),
      fun ρ hre => by_contra fun hlt => hempty ρ (Or.inr ⟨hre, not_le.mp hlt⟩)⟩
  · rintro ⟨h1, h2⟩ n f hf hfc
    have hempty : virtualDefect A B = ∅ := by
      ext ρ
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro (⟨hre, hne⟩ | ⟨hre, hlt⟩)
      · exact hne (h1 ρ hre)
      · exact absurd (h2 ρ hre) (not_le.mpr hlt)
    have hle := negIndex_sub_zeroGram_le_virtualDefect A B hA hB f hf hfc
    rw [hempty, Set.encard_empty] at hle
    exact_mod_cast nonpos_iff_eq_zero.mp hle

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
