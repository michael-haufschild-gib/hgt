import GaloisForLFunctions.HTGeometry.DifferentialOrder
import GaloisForLFunctions.HTGeometry.MeromorphicSimplePoleDifferentialOperator

/-!
# Vanishing-residue clusters obstruct first-order differential equations

For a simple pole, the first-order monomial `f^i * (f')^j` has pole weight `i + 2j`
and leading residue degree `i + j`.  On every fixed pole-weight row these two data
separate the monomials.  Consequently, if the residues in a pole cluster tend to zero,
the uniquely least residue-degree top monomial cannot cancel.

The main theorem below packages the local analytic obstruction.  Infinitely many cluster
centres are used at the application layer to choose a centre away from the finite zero set of
the surviving polynomial coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The derivative of a meromorphic simple pole with residue `ρ` has exact leading coefficient
`-ρ`.  This is the exact-coefficient version of the general derivative-order theorem. -/
theorem tendsto_deriv_of_meromorphicAt_of_simplePoleResidue
    {f : ℂ → ℂ} {p ρ : ℂ} (hf : MeromorphicAt f p) (hρ : ρ ≠ 0)
    (hpole : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 ρ)) :
    Tendsto (fun z : ℂ => (z - p) ^ 2 * deriv f z) (𝓝[≠] p) (𝓝 (-ρ)) := by
  have horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ) := by
    apply meromorphicOrderAt_eq_neg_nat_of_tendsto_pow_mul 1 hf hρ
    simpa using hpole
  obtain ⟨g, hg, hgne, hfacptd⟩ := (meromorphicOrderAt_eq_int_iff hf).mp horder
  have hfac' : f =ᶠ[𝓝[≠] p] fun z => (z - p)⁻¹ * g z := by
    filter_upwards [hfacptd] with z hz
    rw [hz]
    simp [zpow_neg, zpow_one]
  have hgResidue : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 (g p)) := by
    apply (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [hfac', self_mem_nhdsWithin] with z hz hzp
    have hne : z - p ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_ne_zero] using hzp
    rw [hz]
    field_simp [hne]
  have hgp : g p = ρ := tendsto_nhds_unique hgResidue hpole
  have hcomb : {z : ℂ | f z = (z - p)⁻¹ * g z ∧ g z ≠ 0 ∧
      ∀ m : ℕ, ContDiffAt ℂ m g z} ∈ 𝓝[≠] p := by
    filter_upwards [hfac', nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hgne),
      nhdsWithin_le_nhds hg.eventually_analyticAt] with z h1 h2 h3
    exact ⟨h1, h2, fun m => h3.contDiffAt⟩
  rw [Metric.mem_nhdsWithin_iff] at hcomb
  obtain ⟨ε, hε, hsub⟩ := hcomb
  let U := Metric.ball p ε \ {p}
  have hUsub : U ⊆ {z : ℂ | f z = (z - p)⁻¹ * g z ∧ g z ≠ 0 ∧
      ∀ m : ℕ, ContDiffAt ℂ m g z} := by
    intro z hz
    apply hsub
    refine ⟨hz.1, ?_⟩
    simpa [U] using hz.2
  have hUnhds : ∀ᶠ z in 𝓝[≠] p, z ∈ U := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds p hε),
      self_mem_nhdsWithin] with z hb hne
    exact ⟨hb, hne⟩
  have hlim := iteratedDeriv_residue_of_factor_add f g (-p) U
    (fun z hz hzero => hz.2 (by
      simp only [Set.mem_singleton_iff]
      linear_combination hzero))
    (by simpa using hUnhds)
    (fun z hz m => (hUsub hz).2.2 m)
    (by simpa using fun m => hg.contDiffAt)
    (fun z hz => by
      refine Filter.eventuallyEq_of_mem
        ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hz) (fun t ht => ?_)
      show f t = g t * (t + -p)⁻¹
      rw [(hUsub ht).1]
      ring)
    1
  simpa [hgp] using! hlim

/-- Pole order of `f^i * (f')^j` when `f` has a simple pole. -/
def firstOrderPoleWeight (p : ℕ × ℕ) : ℕ := p.1 + 2 * p.2

/-- Power of the residue in the leading term of `f^i * (f')^j`. -/
def firstOrderResidueDegree (p : ℕ × ℕ) : ℕ := p.1 + p.2

/-- At differential order one, pole weight together with residue degree recovers the monomial. -/
theorem firstOrderPoleWeight_residueDegree_injective :
    Function.Injective (fun p : ℕ × ℕ =>
      (firstOrderPoleWeight p, firstOrderResidueDegree p)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  simp only [firstOrderPoleWeight, firstOrderResidueDegree, Prod.mk.injEq] at h ⊢
  omega

/-- Every nonempty finite first-order row has a top pole-weight monomial whose residue degree is
uniquely minimal among the top-weight monomials. -/
theorem exists_firstOrder_topWeight_minResidueDegree
    (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) :
    ∃ p₀ ∈ S,
      (∀ p ∈ S, firstOrderPoleWeight p ≤ firstOrderPoleWeight p₀) ∧
      (∀ p ∈ S, firstOrderPoleWeight p = firstOrderPoleWeight p₀ → p ≠ p₀ →
        firstOrderResidueDegree p₀ < firstOrderResidueDegree p) := by
  classical
  let weights := S.image firstOrderPoleWeight
  have hweights : weights.Nonempty := hS.image _
  let W := weights.max' hweights
  let top := S.filter fun p => firstOrderPoleWeight p = W
  have htop : top.Nonempty := by
    have hWmem : W ∈ weights := Finset.max'_mem weights hweights
    obtain ⟨p, hp, hpW⟩ := Finset.mem_image.mp hWmem
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpW⟩⟩
  let degrees := top.image firstOrderResidueDegree
  have hdegrees : degrees.Nonempty := htop.image _
  let d := degrees.min' hdegrees
  have hdmem : d ∈ degrees := Finset.min'_mem degrees hdegrees
  obtain ⟨p₀, hp₀top, hp₀d⟩ := Finset.mem_image.mp hdmem
  have hp₀S : p₀ ∈ S := (Finset.mem_filter.mp hp₀top).1
  have hp₀W : firstOrderPoleWeight p₀ = W := (Finset.mem_filter.mp hp₀top).2
  refine ⟨p₀, hp₀S, ?_, ?_⟩
  · intro p hp
    have hpweight : firstOrderPoleWeight p ∈ weights := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hle : firstOrderPoleWeight p ≤ W := Finset.le_max' weights _ hpweight
    simpa [hp₀W] using hle
  · intro p hp hpweight hpne
    have hpW : firstOrderPoleWeight p = W := hpweight.trans hp₀W
    have hptop : p ∈ top := Finset.mem_filter.mpr ⟨hp, hpW⟩
    have hpdegree : firstOrderResidueDegree p ∈ degrees :=
      Finset.mem_image.mpr ⟨p, hptop, rfl⟩
    have hdle : d ≤ firstOrderResidueDegree p := Finset.min'_le degrees _ hpdegree
    have hp₀degree : firstOrderResidueDegree p₀ = d := hp₀d
    have hle : firstOrderResidueDegree p₀ ≤ firstOrderResidueDegree p := by
      simpa [hp₀degree] using hdle
    exact lt_of_le_of_ne hle fun heq => hpne <|
      firstOrderPoleWeight_residueDegree_injective <|
        Prod.ext hpweight heq.symm

/-- On one top pole-weight row, a chosen monomial of strictly least residue degree survives when
the nonzero residue tends to zero; every other top-weight monomial disappears after
normalization. -/
theorem tendsto_firstOrderTopResidueRow
    (S : Finset (ℕ × ℕ)) (p₀ : ℕ × ℕ) (hp₀ : p₀ ∈ S)
    (hmin : ∀ p ∈ S, firstOrderPoleWeight p = firstOrderPoleWeight p₀ → p ≠ p₀ →
      firstOrderResidueDegree p₀ < firstOrderResidueDegree p)
    (A : (ℕ × ℕ) → ℕ → ℂ) (a : (ℕ × ℕ) → ℂ)
    (hA : ∀ p ∈ S, Tendsto (A p) atTop (𝓝 (a p)))
    (ρ : ℕ → ℂ) (hρ : Tendsto ρ atTop (𝓝 0)) :
    Tendsto
      (fun m => ∑ p ∈ S,
        if firstOrderPoleWeight p = firstOrderPoleWeight p₀ then
          A p m * (-1 : ℂ) ^ p.2 * ρ m ^
            (firstOrderResidueDegree p - firstOrderResidueDegree p₀)
        else 0)
      atTop (𝓝 (a p₀ * (-1 : ℂ) ^ p₀.2)) := by
  have hterms : ∀ p ∈ S, Tendsto
      (fun m => if firstOrderPoleWeight p = firstOrderPoleWeight p₀ then
          A p m * (-1 : ℂ) ^ p.2 * ρ m ^
            (firstOrderResidueDegree p - firstOrderResidueDegree p₀)
        else 0)
      atTop
      (𝓝 (if p = p₀ then a p₀ * (-1 : ℂ) ^ p₀.2 else 0)) := by
    intro p hp
    by_cases hw : firstOrderPoleWeight p = firstOrderPoleWeight p₀
    · by_cases heq : p = p₀
      · subst p
        simp only [Nat.sub_self, pow_zero, mul_one]
        exact (hA p₀ hp₀).mul_const ((-1 : ℂ) ^ p₀.2)
      · have hdpos : 0 < firstOrderResidueDegree p - firstOrderResidueDegree p₀ := by
          have hlt := hmin p hp hw heq
          omega
        have hpow := hρ.pow (firstOrderResidueDegree p - firstOrderResidueDegree p₀)
        have hpow0 : (0 : ℂ) ^
            (firstOrderResidueDegree p - firstOrderResidueDegree p₀) = 0 :=
          zero_pow hdpos.ne'
        simp only [if_pos hw, if_neg heq]
        convert ((hA p hp).mul_const ((-1 : ℂ) ^ p.2)).mul hpow using 1
        all_goals simp [hpow0]
    · have hne : p ≠ p₀ := by
        intro h
        exact hw (congrArg firstOrderPoleWeight h)
      simp only [if_neg hw, if_neg hne]
      exact tendsto_const_nhds
  have hsum := tendsto_finsetSum S hterms
  have hlimit : (∑ p ∈ S, if p = p₀ then a p₀ * (-1 : ℂ) ^ p₀.2 else 0) =
      a p₀ * (-1 : ℂ) ^ p₀.2 := by
    rw [Finset.sum_eq_single p₀]
    · simp
    · intro p hp hne
      simp [hne]
    · exact fun h => (h hp₀).elim
  rw [hlimit] at hsum
  exact hsum

/-- The normalized top residue row is eventually nonzero when its unique surviving coefficient
is nonzero. -/
theorem eventually_firstOrderTopResidueRow_ne_zero
    (S : Finset (ℕ × ℕ)) (p₀ : ℕ × ℕ) (hp₀ : p₀ ∈ S)
    (hmin : ∀ p ∈ S, firstOrderPoleWeight p = firstOrderPoleWeight p₀ → p ≠ p₀ →
      firstOrderResidueDegree p₀ < firstOrderResidueDegree p)
    (A : (ℕ × ℕ) → ℕ → ℂ) (a : (ℕ × ℕ) → ℂ)
    (hA : ∀ p ∈ S, Tendsto (A p) atTop (𝓝 (a p)))
    (ha : a p₀ ≠ 0)
    (ρ : ℕ → ℂ) (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∀ᶠ m in atTop,
      (∑ p ∈ S,
        if firstOrderPoleWeight p = firstOrderPoleWeight p₀ then
          A p m * (-1 : ℂ) ^ p.2 * ρ m ^
            (firstOrderResidueDegree p - firstOrderResidueDegree p₀)
        else 0) ≠ 0 := by
  have hlim := tendsto_firstOrderTopResidueRow S p₀ hp₀ hmin A a hA ρ hρ
  have htarget : a p₀ * (-1 : ℂ) ^ p₀.2 ≠ 0 :=
    mul_ne_zero ha (pow_ne_zero _ (by norm_num))
  exact hlim.eventually_ne htarget

/-- A finite polynomial-coefficient row in `f` and `f'`. -/
def firstOrderPolynomialRowEval
    (S : Finset (ℕ × ℕ)) (A : (ℕ × ℕ) → Polynomial ℂ)
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ p ∈ S, (A p).eval z * f z ^ p.1 * deriv f z ^ p.2

/-! ## Canonical first-order rows

The first variable of a differential polynomial is `z`; the remaining two variables are `f` and
`f'`.  The following normal form moves powers of `z` into polynomial coefficients and identifies a
finitely supported exponent vector on `Fin 2` with the pair of exponents of `f` and `f'`.
-/

/-- The pair of exponents represented by a finitely supported function on `Fin 2`. -/
def finTwoExponentPair (d : Fin 2 →₀ ℕ) : ℕ × ℕ := (d 0, d 1)

/-- The finitely supported exponent vector represented by a pair. -/
def exponentPairFinTwo (p : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cases p.1 (fun _ => p.2))

@[simp] theorem finTwoExponentPair_exponentPairFinTwo (p : ℕ × ℕ) :
    finTwoExponentPair (exponentPairFinTwo p) = p := by
  ext <;> rfl

@[simp] theorem exponentPairFinTwo_finTwoExponentPair (d : Fin 2 →₀ ℕ) :
    exponentPairFinTwo (finTwoExponentPair d) = d := by
  apply Finsupp.ext
  intro i
  fin_cases i <;> rfl

theorem finTwoExponentPair_injective : Function.Injective finTwoExponentPair :=
  Function.LeftInverse.injective exponentPairFinTwo_finTwoExponentPair

/-- The canonical polynomial row in the variables `f,f'` with coefficients in `ℂ[z]` associated
to a differential polynomial in the variables `z,f,f'`. -/
def firstOrderRowPolynomial (P : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 2) (Polynomial ℂ) :=
  MvPolynomial.optionEquivRight ℂ (Fin 2)
    (MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv 2) P)

def firstOrderRowSupport (P : MvPolynomial (Fin 3) ℂ) : Finset (ℕ × ℕ) :=
  (firstOrderRowPolynomial P).support.image finTwoExponentPair

def firstOrderRowCoefficient (P : MvPolynomial (Fin 3) ℂ) (p : ℕ × ℕ) :
    Polynomial ℂ :=
  (firstOrderRowPolynomial P).coeff (exponentPairFinTwo p)

theorem firstOrderRowPolynomial_ne_zero {P : MvPolynomial (Fin 3) ℂ} (hP : P ≠ 0) :
    firstOrderRowPolynomial P ≠ 0 := by
  exact (MvPolynomial.optionEquivRight ℂ (Fin 2)).injective.ne
    ((MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv 2)).injective.ne hP)

theorem firstOrderRowSupport_nonempty {P : MvPolynomial (Fin 3) ℂ} (hP : P ≠ 0) :
    (firstOrderRowSupport P).Nonempty := by
  rw [firstOrderRowSupport, Finset.image_nonempty]
  apply Finsupp.support_nonempty_iff.mpr
  intro hcoeff
  apply firstOrderRowPolynomial_ne_zero hP
  apply AddMonoidAlgebra.coeff_injective
  simpa using hcoeff

theorem firstOrderRowCoefficient_ne_zero {P : MvPolynomial (Fin 3) ℂ}
    {p : ℕ × ℕ} (hp : p ∈ firstOrderRowSupport P) :
    firstOrderRowCoefficient P p ≠ 0 := by
  rw [firstOrderRowSupport, Finset.mem_image] at hp
  obtain ⟨d, hd, rfl⟩ := hp
  simpa [firstOrderRowCoefficient] using (MvPolynomial.mem_support_iff.mp hd)

/-- Evaluating the canonical row polynomial agrees with evaluating the original differential
polynomial after assigning `z,x,y` to its three variables. -/
theorem firstOrderRowPolynomial_eval
    (P : MvPolynomial (Fin 3) ℂ) (z x y : ℂ) :
    MvPolynomial.eval (Fin.cons z (Fin.cons x (fun _ => y))) P =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z) (Fin.cases x (fun _ => y))
        (firstOrderRowPolynomial P) := by
  let lhs : MvPolynomial (Fin 3) ℂ →+* ℂ :=
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (Fin.cons z (Fin.cons x (fun _ => y)))
  let rhs : MvPolynomial (Fin 3) ℂ →+* ℂ :=
    (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z) (Fin.cases x (fun _ => y))).comp
      ((MvPolynomial.optionEquivRight ℂ (Fin 2)).toRingEquiv.toRingHom.comp
        (MvPolynomial.renameEquiv ℂ (_root_.finSuccEquiv 2)).toRingEquiv.toRingHom)
  change lhs P = rhs P
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs]
    · intro i
      fin_cases i
      · norm_num [lhs, rhs, _root_.finSuccEquiv, _root_.finSuccEquiv']
      · norm_num [lhs, rhs, _root_.finSuccEquiv, _root_.finSuccEquiv']
      · change lhs (MvPolynomial.X (2 : Fin 3)) =
          rhs (MvPolynomial.X (2 : Fin 3))
        have hmap : (_root_.finSuccEquiv 2) (2 : Fin 3) = some (1 : Fin 2) := by
          exact _root_.finSuccEquiv_succ (1 : Fin 2)
        simp [lhs, rhs, hmap]
        rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) by rfl, Fin.cons_succ]
        rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl, Fin.cons_succ, Fin.cases_succ]
  rw [hhom]

/-- The explicit finite row and the canonical multivariable row polynomial have identical
evaluations. -/
theorem firstOrderPolynomialRowEval_eq_mvPolynomial_eval₂
    (Q : MvPolynomial (Fin 2) (Polynomial ℂ)) (f : ℂ → ℂ) (z : ℂ) :
    firstOrderPolynomialRowEval
        (Q.support.image finTwoExponentPair)
        (fun p => Q.coeff (exponentPairFinTwo p)) f z =
      MvPolynomial.eval₂ (Polynomial.evalRingHom z)
        (Fin.cases (f z) (fun _ => deriv f z)) Q := by
  rw [MvPolynomial.eval₂_eq']
  simp only [firstOrderPolynomialRowEval]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [exponentPairFinTwo_finTwoExponentPair]
    simp only [finTwoExponentPair]
    rw [Fin.prod_univ_two]
    change Polynomial.eval z (Q.coeff d) * f z ^ d 0 * deriv f z ^ d 1 =
      Polynomial.eval z (Q.coeff d) * (f z ^ d 0 * deriv f z ^ d 1)
    ring
  · exact fun a _ b _ hab => finTwoExponentPair_injective hab

private theorem firstOrder_scale_monomial
    (W i j : ℕ) (hweight : i + 2 * j ≤ W) (t a x y : ℂ) :
    t ^ W * (a * x ^ i * y ^ j) =
      a * (t * x) ^ i * (t ^ 2 * y) ^ j * t ^ (W - (i + 2 * j)) := by
  simp only [mul_pow]
  have hexp : i + 2 * j + (W - (i + 2 * j)) = W := Nat.add_sub_of_le hweight
  rw [show (t ^ 2) ^ j = t ^ (2 * j) by rw [← pow_mul]]
  calc
    t ^ W * (a * x ^ i * y ^ j) = a * x ^ i * y ^ j * t ^ W := by ring
    _ = a * x ^ i * y ^ j *
        (t ^ i * t ^ (2 * j) * t ^ (W - (i + 2 * j))) := by
      rw [← pow_add, ← pow_add, hexp]
    _ = a * (t ^ i * x ^ i) * (t ^ (2 * j) * y ^ j) *
        t ^ (W - (i + 2 * j)) := by ring

/-- **Local vanishing-residue first-order obstruction.**  Consider a finite first-order
polynomial row and a top pole-weight monomial whose residue degree is uniquely minimal on that
top row.  If one cluster of simple poles approaches a centre where the pivot coefficient is
nonzero and the nonzero residues tend to zero, the row cannot vanish identically.

This is the analytic engine used after choosing, from infinitely many cluster centres, one that
avoids the finite zero set of the pivot coefficient polynomial. -/
theorem exists_firstOrderPolynomialRowEval_ne_zero_of_vanishingResidueCluster
    (S : Finset (ℕ × ℕ)) (A : (ℕ × ℕ) → Polynomial ℂ)
    (p₀ : ℕ × ℕ) (hp₀ : p₀ ∈ S)
    (htop : ∀ p ∈ S, firstOrderPoleWeight p ≤ firstOrderPoleWeight p₀)
    (hmin : ∀ p ∈ S, firstOrderPoleWeight p = firstOrderPoleWeight p₀ → p ≠ p₀ →
      firstOrderResidueDegree p₀ < firstOrderResidueDegree p)
    (f : ℂ → ℂ) (a : ℂ) (z ρ : ℕ → ℂ)
    (hz : Tendsto z atTop (𝓝 a))
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hρne : ∀ m, ρ m ≠ 0)
    (hf : ∀ m, Tendsto (fun w => (w - z m) * f w)
      (𝓝[≠] (z m)) (𝓝 (ρ m)))
    (hdf : ∀ m, Tendsto (fun w => (w - z m) ^ 2 * deriv f w)
      (𝓝[≠] (z m)) (𝓝 (-ρ m)))
    (hA₀ : (A p₀).eval a ≠ 0) :
    ∃ w : ℂ, firstOrderPolynomialRowEval S A f w ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  let W := firstOrderPoleWeight p₀
  let d := firstOrderResidueDegree p₀
  have hleading : ∀ m,
      (∑ p ∈ S, if firstOrderPoleWeight p = W then
        (A p).eval (z m) * (-1 : ℂ) ^ p.2 * ρ m ^ firstOrderResidueDegree p
      else 0) = 0 := by
    intro m
    have ht0 : Tendsto (fun w : ℂ => w - z m) (𝓝[≠] (z m)) (𝓝 0) := by
      have h : ContinuousAt (fun w : ℂ => w - z m) (z m) :=
        (continuous_id.sub continuous_const).continuousAt
      have h' : Tendsto (fun w : ℂ => w - z m) (𝓝 (z m)) (𝓝 0) := by
        simpa using h.tendsto
      exact h'.mono_left nhdsWithin_le_nhds
    have hterms : ∀ p ∈ S, Tendsto
        (fun w => (w - z m) ^ W *
          ((A p).eval w * f w ^ p.1 * deriv f w ^ p.2))
        (𝓝[≠] (z m))
        (𝓝 (if firstOrderPoleWeight p = W then
          (A p).eval (z m) * (-1 : ℂ) ^ p.2 *
            ρ m ^ firstOrderResidueDegree p
        else 0)) := by
      intro p hp
      have hpw := htop p hp
      have hcoeff : Tendsto (fun w : ℂ => (A p).eval w)
          (𝓝[≠] (z m)) (𝓝 ((A p).eval (z m))) :=
        (A p).continuous.continuousAt.continuousWithinAt
      have hraw := (((hcoeff.mul ((hf m).pow p.1)).mul ((hdf m).pow p.2)).mul
        (ht0.pow (W - firstOrderPoleWeight p)))
      have hfun : (fun w => (w - z m) ^ W *
          ((A p).eval w * f w ^ p.1 * deriv f w ^ p.2)) =
          fun w => (A p).eval w * ((w - z m) * f w) ^ p.1 *
            ((w - z m) ^ 2 * deriv f w) ^ p.2 *
              (w - z m) ^ (W - firstOrderPoleWeight p) := by
        funext w
        exact firstOrder_scale_monomial W p.1 p.2 hpw (w - z m)
          ((A p).eval w) (f w) (deriv f w)
      rw [hfun]
      by_cases hw : firstOrderPoleWeight p = W
      · have hgap : W - firstOrderPoleWeight p = 0 := by omega
        simp only [hw, if_pos] at hraw ⊢
        simp only [Nat.sub_self, pow_zero, mul_one] at hraw
        have hval : (A p).eval (z m) * ρ m ^ p.1 * (-ρ m) ^ p.2 =
            (A p).eval (z m) * (-1 : ℂ) ^ p.2 *
              ρ m ^ firstOrderResidueDegree p := by
          rw [neg_pow (ρ m) p.2]
          simp only [firstOrderResidueDegree, pow_add]
          ring
        rw [hval] at hraw
        simpa [hgap] using hraw
      · have hgap : 0 < W - firstOrderPoleWeight p := by
          have hle := hpw
          omega
        have hzero : (0 : ℂ) ^ (W - firstOrderPoleWeight p) = 0 :=
          zero_pow hgap.ne'
        simp only [hw, hzero, mul_zero] at hraw ⊢
        exact hraw
    have hsum := tendsto_finsetSum S hterms
    have hsum' : Tendsto
        (fun w => (w - z m) ^ W * firstOrderPolynomialRowEval S A f w)
        (𝓝[≠] (z m))
        (𝓝 (∑ p ∈ S, if firstOrderPoleWeight p = W then
          (A p).eval (z m) * (-1 : ℂ) ^ p.2 *
            ρ m ^ firstOrderResidueDegree p else 0)) := by
      convert hsum using 1
      funext w
      simp only [firstOrderPolynomialRowEval, Finset.mul_sum]
    have hzero : Tendsto
        (fun w => (w - z m) ^ W * firstOrderPolynomialRowEval S A f w)
        (𝓝[≠] (z m)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards with w
      rw [hcon w, mul_zero]
    exact (tendsto_nhds_unique hsum' hzero)
  let C : (ℕ × ℕ) → ℕ → ℂ := fun p m => (A p).eval (z m)
  let c : (ℕ × ℕ) → ℂ := fun p => (A p).eval a
  have hC : ∀ p ∈ S, Tendsto (C p) atTop (𝓝 (c p)) := by
    intro p _
    exact (A p).continuous.continuousAt.tendsto.comp hz
  have hnormalized_ne := eventually_firstOrderTopResidueRow_ne_zero
    S p₀ hp₀ hmin C c hC hA₀ ρ hρ
  have hnormalized_zero : ∀ m,
      (∑ p ∈ S, if firstOrderPoleWeight p = firstOrderPoleWeight p₀ then
        C p m * (-1 : ℂ) ^ p.2 *
          ρ m ^ (firstOrderResidueDegree p - d)
      else 0) = 0 := by
    intro m
    have hfactor :
        (∑ p ∈ S, if firstOrderPoleWeight p = W then
          (A p).eval (z m) * (-1 : ℂ) ^ p.2 *
            ρ m ^ firstOrderResidueDegree p else 0) =
        ρ m ^ d *
          (∑ p ∈ S, if firstOrderPoleWeight p = firstOrderPoleWeight p₀ then
            C p m * (-1 : ℂ) ^ p.2 *
              ρ m ^ (firstOrderResidueDegree p - d) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hw : firstOrderPoleWeight p = firstOrderPoleWeight p₀
      · have hdle : d ≤ firstOrderResidueDegree p := by
          by_cases heq : p = p₀
          · subst p
            exact le_rfl
          · exact (hmin p hp hw heq).le
        simp only [W, hw, if_pos, C]
        calc
          (A p).eval (z m) * (-1 : ℂ) ^ p.2 *
              ρ m ^ firstOrderResidueDegree p =
              ((A p).eval (z m) * (-1 : ℂ) ^ p.2) *
                ρ m ^ firstOrderResidueDegree p := by ring
          _ = ((A p).eval (z m) * (-1 : ℂ) ^ p.2) *
                (ρ m ^ d * ρ m ^ (firstOrderResidueDegree p - d)) := by
              rw [← pow_add, Nat.add_sub_of_le hdle]
          _ = ρ m ^ d * ((A p).eval (z m) * (-1 : ℂ) ^ p.2) *
                ρ m ^ (firstOrderResidueDegree p - d) := by ring
          _ = ρ m ^ d * ((A p).eval (z m) * (-1 : ℂ) ^ p.2 *
                ρ m ^ (firstOrderResidueDegree p - d)) := by ring
      · have hwW : firstOrderPoleWeight p ≠ W := by simpa [W] using hw
        simp [hw, hwW]
    have hzlead := hleading m
    rw [hfactor] at hzlead
    exact (mul_eq_zero.mp hzlead).resolve_left (pow_ne_zero _ (hρne m))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hnormalized_ne)
  exact (hN N le_rfl) (hnormalized_zero N)

/-- A nonzero polynomial cannot vanish on an injective infinite sequence. -/
theorem exists_polynomial_eval_ne_of_injective
    (P : Polynomial ℂ) (hP : P ≠ 0) (a : ℕ → ℂ) (ha : Function.Injective a) :
    ∃ n, P.eval (a n) ≠ 0 := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := a) ha
  intro n
  exact h n

/-- **Infinitely many vanishing-residue clusters exclude every fixed first-order row.**
If every coefficient listed in a nonempty finite row is nonzero, an injective family of cluster
centres supplies a centre where the unique top-weight/minimal-residue-degree coefficient does not
vanish.  The local obstruction then proves that the row is not an identity.

Taking `S` to be the support of a cleared first-order ADE gives the paper-level statement that a
function with these clusters satisfies no first-order algebraic differential equation over
`ℂ(z)`. -/
theorem exists_firstOrderPolynomialRowEval_ne_zero_of_infiniteVanishingResidueClusters
    (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (A : (ℕ × ℕ) → Polynomial ℂ) (hA : ∀ p ∈ S, A p ≠ 0)
    (f : ℂ → ℂ) (a : ℕ → ℂ) (ha : Function.Injective a)
    (z ρ : ℕ → ℕ → ℂ)
    (hz : ∀ n, Tendsto (z n) atTop (𝓝 (a n)))
    (hρ : ∀ n, Tendsto (ρ n) atTop (𝓝 0))
    (hρne : ∀ n m, ρ n m ≠ 0)
    (hf : ∀ n m, Tendsto (fun w => (w - z n m) * f w)
      (𝓝[≠] (z n m)) (𝓝 (ρ n m)))
    (hdf : ∀ n m, Tendsto (fun w => (w - z n m) ^ 2 * deriv f w)
      (𝓝[≠] (z n m)) (𝓝 (-ρ n m))) :
    ∃ w : ℂ, firstOrderPolynomialRowEval S A f w ≠ 0 := by
  obtain ⟨p₀, hp₀, htop, hmin⟩ := exists_firstOrder_topWeight_minResidueDegree S hS
  obtain ⟨n, hn⟩ := exists_polynomial_eval_ne_of_injective (A p₀) (hA p₀ hp₀) a ha
  exact exists_firstOrderPolynomialRowEval_ne_zero_of_vanishingResidueCluster
    S A p₀ hp₀ htop hmin f (a n) (z n) (ρ n) (hz n) (hρ n)
      (hρne n) (hf n) (hdf n) hn

end

end GaloisForLFunctions.HTGeometry
