import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticJetHilbertRigging

/-!
# Closed source Frobenius on Deninger jet Hilbert cohomology

The compact-open source Frobenius is multiplication by `1/2 + I z`.  Leibniz therefore forces its
full multiplicity-jet action:

`(Theta a)_(rho,k) = (1/2 + I rho) a_(rho,k) + k I a_(rho,k-1)`.

The second term is the exact local nilpotent Jordan contribution; it is not inserted from a
divisor model.  This file derives the formula from source differentiation and constructs its
maximal square-summable `LinearPMap`.  The operator has closed graph, dense finite-jet domain, and
intertwines exactly with compact-open arithmetic Frobenius through the canonical Gelfand
distribution embedding.

No RH, positivity, zero-location, or simplicity hypothesis is used.
-/

open Complex Function Set Topology

namespace RHTower

noncomputable section

/-- All derivatives of the affine weight-one Frobenius coordinate. -/
theorem deningerArithmeticThetaCoordinate_iteratedDeriv
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => 1 / 2 + Complex.I * w) z =
      if n = 0 then 1 / 2 + Complex.I * z
      else if n = 1 then Complex.I else 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [iteratedDeriv_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    rw [iteratedDeriv_const_add hnpos (1 / 2 : ℂ)]
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_fun_id]
    simp [hn0]

/-- Leibniz formula for every source Frobenius jet, with its zero-order branch displayed. -/
theorem deningerCompactOpenThetaMul_iteratedDeriv
    (F : DeningerCompactOpenEntire)
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n
        (deningerCompactOpenThetaMul F : ℂ → ℂ) z =
      (1 / 2 + Complex.I * z) *
          iteratedDeriv n (F : ℂ → ℂ) z +
        if n = 0 then 0
        else (n : ℂ) * Complex.I *
          iteratedDeriv (n - 1) (F : ℂ → ℂ) z := by
  have htheta :
      (deningerCompactOpenThetaMul F : ℂ → ℂ) =
        (fun w : ℂ => 1 / 2 + Complex.I * w) *
          (F : ℂ → ℂ) := by
    funext w
    exact deningerCompactOpenThetaMul_apply F w
  rw [htheta]
  rw [iteratedDeriv_mul
    (f := fun w : ℂ => 1 / 2 + Complex.I * w)
    (g := (F : ℂ → ℂ))
    (by fun_prop) (F.2.analyticAt z).contDiffAt]
  simp_rw [deningerArithmeticThetaCoordinate_iteratedDeriv]
  by_cases hn0 : n = 0
  · subst n
    simp
  · have h1mem : 1 ∈ Finset.range (n + 1) := by
      simp
      omega
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h1mem]
    simp only [if_true, Nat.choose_one_right]
    have hrest :
        ∑ i ∈ Finset.range (n + 1) \ {1},
            (n.choose i : ℂ) *
              (if i = 0 then 1 / 2 + Complex.I * z
                else if i = 1 then Complex.I else 0) *
              iteratedDeriv (n - i) (F : ℂ → ℂ) z =
          (1 / 2 + Complex.I * z) *
            iteratedDeriv n (F : ℂ → ℂ) z := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b hb hb0
        simp only [Finset.mem_sdiff, Finset.mem_range,
          Finset.mem_singleton] at hb
        simp [hb0, hb.2]
      · simp
    rw [hrest]
    simp [hn0]
    ring

/-- Branch-free form of the source jet formula; the predecessor coefficient vanishes at `n=0`. -/
theorem deningerCompactOpenThetaMul_iteratedDeriv'
    (F : DeningerCompactOpenEntire)
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n
        (deningerCompactOpenThetaMul F : ℂ → ℂ) z =
      (1 / 2 + Complex.I * z) *
          iteratedDeriv n (F : ℂ → ℂ) z +
        (n : ℂ) * Complex.I *
          iteratedDeriv (n - 1) (F : ℂ → ℂ) z := by
  rw [deningerCompactOpenThetaMul_iteratedDeriv]
  by_cases hn : n = 0
  · subst n
    simp
  · simp [hn]

/-- Predecessor jet index; at zero it remains zero, where its coefficient vanishes. -/
def deningerArithmeticJetIndexPred
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    DeningerArithmeticJetIndex rho :=
  ⟨k.val - 1, by
    have hm := xiSupportMultiplicity_pos rho
    omega⟩

@[simp]
theorem deningerArithmeticJetIndexPred_val
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    (deningerArithmeticJetIndexPred rho k).val = k.val - 1 :=
  rfl

/-- Exact full-jet Frobenius law on compact-open arithmetic cohomology. -/
theorem deningerCompactOpenH1AllJets_theta
    (x : DeningerArithmeticCompactOpenH1)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerCompactOpenH1AllJets
        (deningerCompactOpenTheta x) rho k =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) *
          deningerCompactOpenH1AllJets x rho k +
        (k.val : ℂ) * Complex.I *
          deningerCompactOpenH1AllJets x rho
            (deningerArithmeticJetIndexPred rho k) := by
  obtain ⟨F, rfl⟩ := Quotient.exists_rep x
  change
    deningerCompactOpenH1AllJets
        (deningerCompactOpenTheta
          (deningerArithmeticCompactOpenH1Class F)) rho k =
      (1 / 2 + Complex.I * xiSpectralPointSupport rho) *
          deningerCompactOpenH1AllJets
            (deningerArithmeticCompactOpenH1Class F) rho k +
        (k.val : ℂ) * Complex.I *
          deningerCompactOpenH1AllJets
            (deningerArithmeticCompactOpenH1Class F) rho
              (deningerArithmeticJetIndexPred rho k)
  rw [deningerCompactOpenTheta_class,
    deningerCompactOpenH1AllJets_class,
    deningerCompactOpenH1AllJets_class]
  exact deningerCompactOpenThetaMul_iteratedDeriv' F k
    (xiSpectralPointSupport rho)

/-- Coordinate function of the maximal jet Frobenius operator. -/
def deningerArithmeticJetThetaValue
    (a : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) : ℂ :=
  (1 / 2 + Complex.I * xiSpectralPointSupport q.1) * a q +
    (q.2.val : ℂ) * Complex.I *
      a ⟨q.1, deningerArithmeticJetIndexPred q.1 q.2⟩

theorem deningerArithmeticJetThetaValue_add
    (a b : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerArithmeticJetThetaValue (a + b) q =
      deningerArithmeticJetThetaValue a q +
        deningerArithmeticJetThetaValue b q := by
  simp only [deningerArithmeticJetThetaValue,
    lp.coeFn_add, Pi.add_apply]
  ring

theorem deningerArithmeticJetThetaValue_smul
    (c : ℂ) (a : DeningerArithmeticJetHilbert)
    (q : DeningerArithmeticJetCoordinate) :
    deningerArithmeticJetThetaValue (c • a) q =
      c * deningerArithmeticJetThetaValue a q := by
  simp only [deningerArithmeticJetThetaValue,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Maximal `ell^(2 : ℕ)` domain of source jet Frobenius. -/
def deningerArithmeticJetThetaDomain :
    Submodule ℂ DeningerArithmeticJetHilbert where
  carrier := {a | Memℓp (deningerArithmeticJetThetaValue a) 2}
  zero_mem' := by
    have hzero :
        deningerArithmeticJetThetaValue
            (0 : DeningerArithmeticJetHilbert) =
          fun _ => 0 := by
      funext q
      change
        (1 / 2 + Complex.I * xiSpectralPointSupport q.1) * 0 +
          (q.2.val : ℂ) * Complex.I * 0 = 0
      ring
    change Memℓp
      (deningerArithmeticJetThetaValue
        (0 : DeningerArithmeticJetHilbert)) 2
    rw [hzero]
    exact zero_memℓp
  add_mem' := by
    intro a b ha hb
    change Memℓp (deningerArithmeticJetThetaValue (a + b)) 2
    change Memℓp (deningerArithmeticJetThetaValue a) 2 at ha
    change Memℓp (deningerArithmeticJetThetaValue b) 2 at hb
    rw [show deningerArithmeticJetThetaValue (a + b) =
        deningerArithmeticJetThetaValue a +
          deningerArithmeticJetThetaValue b by
      funext q
      exact deningerArithmeticJetThetaValue_add a b q]
    exact ha.add hb
  smul_mem' := by
    intro c a ha
    change Memℓp (deningerArithmeticJetThetaValue (c • a)) 2
    change Memℓp (deningerArithmeticJetThetaValue a) 2 at ha
    rw [show deningerArithmeticJetThetaValue (c • a) =
        c • deningerArithmeticJetThetaValue a by
      funext q
      exact deningerArithmeticJetThetaValue_smul c a q]
    exact ha.const_smul c

/-- Maximal closed source Frobenius on canonical jet Hilbert cohomology. -/
def deningerArithmeticJetClosedTheta :
    DeningerArithmeticJetHilbert →ₗ.[ℂ]
      DeningerArithmeticJetHilbert where
  domain := deningerArithmeticJetThetaDomain
  toFun :=
    { toFun := fun a =>
        ⟨deningerArithmeticJetThetaValue a, a.property⟩
      map_add' := by
        intro a b
        ext q
        exact deningerArithmeticJetThetaValue_add a b q
      map_smul' := by
        intro c a
        ext q
        exact deningerArithmeticJetThetaValue_smul c a q }

@[simp]
theorem deningerArithmeticJetClosedTheta_apply
    (a : deningerArithmeticJetClosedTheta.domain)
    (q : DeningerArithmeticJetCoordinate) :
    deningerArithmeticJetClosedTheta a q =
      deningerArithmeticJetThetaValue a q :=
  rfl

/-- Coordinate graph defect of the source jet Frobenius. -/
def deningerArithmeticJetThetaGraphDefect
    (q : DeningerArithmeticJetCoordinate) :
    (DeningerArithmeticJetHilbert ×
      DeningerArithmeticJetHilbert) →L[ℂ] ℂ :=
  (lp.evalCLM ℂ
      (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q).comp
      (ContinuousLinearMap.snd ℂ
        DeningerArithmeticJetHilbert
        DeningerArithmeticJetHilbert) -
    (1 / 2 + Complex.I * xiSpectralPointSupport q.1) •
      (lp.evalCLM ℂ
        (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q).comp
        (ContinuousLinearMap.fst ℂ
          DeningerArithmeticJetHilbert
          DeningerArithmeticJetHilbert) -
    ((q.2.val : ℂ) * Complex.I) •
      (lp.evalCLM ℂ
        (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2
          ⟨q.1, deningerArithmeticJetIndexPred q.1 q.2⟩).comp
        (ContinuousLinearMap.fst ℂ
          DeningerArithmeticJetHilbert
          DeningerArithmeticJetHilbert)

/-- The operator graph is the intersection of its continuous coordinate equations. -/
theorem deningerArithmeticJetClosedTheta_graph_eq :
    deningerArithmeticJetClosedTheta.graph =
      ⨅ q : DeningerArithmeticJetCoordinate,
        (deningerArithmeticJetThetaGraphDefect q).ker := by
  ext p
  constructor
  · intro hp
    rw [LinearPMap.mem_graph_iff] at hp
    rcases hp with ⟨a, ha, hout⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro q
    change p.2 q -
        (1 / 2 + Complex.I * xiSpectralPointSupport q.1) * p.1 q -
        ((q.2.val : ℂ) * Complex.I) *
          p.1 ⟨q.1, deningerArithmeticJetIndexPred q.1 q.2⟩ = 0
    rw [← ha, ← hout]
    simp [deningerArithmeticJetThetaValue]
  · intro hp
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hp
    have hcoord : ∀ q : DeningerArithmeticJetCoordinate,
        p.2 q = deningerArithmeticJetThetaValue p.1 q := by
      intro q
      have hq := hp q
      change p.2 q -
          (1 / 2 + Complex.I * xiSpectralPointSupport q.1) * p.1 q -
          ((q.2.val : ℂ) * Complex.I) *
            p.1
              ⟨q.1, deningerArithmeticJetIndexPred q.1 q.2⟩ = 0 at hq
      unfold deningerArithmeticJetThetaValue
      linear_combination hq
    have hdom : p.1 ∈ deningerArithmeticJetThetaDomain := by
      change Memℓp (deningerArithmeticJetThetaValue p.1) 2
      rw [show deningerArithmeticJetThetaValue p.1 =
          fun q => p.2 q by
        funext q
        exact (hcoord q).symm]
      exact lp.memℓp p.2
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨p.1, hdom⟩, rfl, ?_⟩
    ext q
    exact (hcoord q).symm

/-- Source jet Frobenius has closed graph on its maximal domain. -/
theorem deningerArithmeticJetClosedTheta_isClosed :
    deningerArithmeticJetClosedTheta.IsClosed := by
  rw [LinearPMap.IsClosed,
    deningerArithmeticJetClosedTheta_graph_eq]
  change IsClosed
    ((↑(⨅ q : DeningerArithmeticJetCoordinate,
      (deningerArithmeticJetThetaGraphDefect q).ker) :
      Set (DeningerArithmeticJetHilbert ×
        DeningerArithmeticJetHilbert)))
  rw [show
      ((↑(⨅ q : DeningerArithmeticJetCoordinate,
        (deningerArithmeticJetThetaGraphDefect q).ker) :
        Set (DeningerArithmeticJetHilbert ×
          DeningerArithmeticJetHilbert))) =
        ⋂ q : DeningerArithmeticJetCoordinate,
          ((deningerArithmeticJetThetaGraphDefect q).ker :
            Set (DeningerArithmeticJetHilbert ×
              DeningerArithmeticJetHilbert)) by
    ext p
    simp]
  exact isClosed_iInter fun q =>
    (deningerArithmeticJetThetaGraphDefect q).isClosed_ker

/-- Every one-coordinate jet vector lies in the maximal Frobenius domain. -/
theorem deningerArithmeticJetBasis_mem_thetaDomain
    (q : DeningerArithmeticJetCoordinate) :
    lp.single 2 q 1 ∈ deningerArithmeticJetThetaDomain := by
  change Memℓp
    (deningerArithmeticJetThetaValue (lp.single 2 q 1)) 2
  apply (memℓp_zero ?_).of_exponent_ge
    (by norm_num : (0 : ENNReal) ≤ 2)
  refine (Set.finite_range
      (fun k : DeningerArithmeticJetIndex q.1 =>
        (⟨q.1, k⟩ : DeningerArithmeticJetCoordinate))).subset ?_
  intro r hr
  by_cases hfirst : r.1 = q.1
  · rcases r with ⟨rho, k⟩
    change rho = q.1 at hfirst
    cases hfirst
    exact ⟨k, rfl⟩
  · exfalso
    apply hr
    have hrq : r ≠ q := by
      intro h
      exact hfirst
        (congrArg
          (fun s : DeningerArithmeticJetCoordinate => s.1) h)
    have hpredq :
        (⟨r.1, deningerArithmeticJetIndexPred r.1 r.2⟩ :
          DeningerArithmeticJetCoordinate) ≠ q := by
      intro h
      have hfst :
          (⟨r.1, deningerArithmeticJetIndexPred r.1 r.2⟩ :
            DeningerArithmeticJetCoordinate).1 = q.1 :=
        congrArg
          (fun s : DeningerArithmeticJetCoordinate => s.1) h
      exact hfirst hfst
    simp [deningerArithmeticJetThetaValue, lp.single_apply,
      hrq, hpredq]

/-- Every algebraic finite-support test jet lies in the maximal Frobenius domain. -/
theorem deningerArithmeticJetTestToHilbert_mem_thetaDomain
    (a : DeningerArithmeticJetTest) :
    deningerArithmeticJetTestToHilbert a ∈
      deningerArithmeticJetThetaDomain := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      simp
  | single_add q c a hq _hc ih =>
      rw [map_add, deningerArithmeticJetTestToHilbert_single]
      apply deningerArithmeticJetThetaDomain.add_mem
      · have hb :=
          deningerArithmeticJetThetaDomain.smul_mem c
            (deningerArithmeticJetBasis_mem_thetaDomain q)
        simpa only [← lp.single_smul, smul_eq_mul, mul_one] using hb
      · exact ih

/-- The maximal closed source Frobenius has dense finite-jet domain. -/
theorem deningerArithmeticJetClosedTheta_dense :
    Dense (deningerArithmeticJetClosedTheta.domain :
      Set DeningerArithmeticJetHilbert) := by
  exact deningerArithmeticJetTestToHilbert_dense.mono
    (by
      rintro _ ⟨a, rfl⟩
      exact deningerArithmeticJetTestToHilbert_mem_thetaDomain a)

/--
The closed jet generator intertwines exactly with source compact-open Frobenius through the
Hilbert-to-distribution embedding.
-/
theorem deningerArithmeticJetClosedTheta_distribution
    (a : deningerArithmeticJetClosedTheta.domain) :
    deningerArithmeticJetHilbertToH1
        (deningerArithmeticJetClosedTheta a) =
      deningerCompactOpenTheta
        (deningerArithmeticJetHilbertToH1
          (a : DeningerArithmeticJetHilbert)) := by
  apply deningerCompactOpenH1AllJets_injective
  funext rho k
  rw [deningerCompactOpenH1AllJets_theta]
  rw [deningerCompactOpenH1AllJets_apply,
    deningerCompactOpenH1AllJets_apply,
    deningerCompactOpenH1AllJets_apply]
  rw [deningerCompactOpenH1Jet_jetHilbertToH1
      (⟨rho, k⟩ : DeningerArithmeticJetCoordinate)
      (deningerArithmeticJetClosedTheta a),
    deningerCompactOpenH1Jet_jetHilbertToH1
      (⟨rho, k⟩ : DeningerArithmeticJetCoordinate)
      (a : DeningerArithmeticJetHilbert),
    deningerCompactOpenH1Jet_jetHilbertToH1
      (⟨rho, deningerArithmeticJetIndexPred rho k⟩ :
        DeningerArithmeticJetCoordinate)
      (a : DeningerArithmeticJetHilbert)]
  rfl

/-- The affine Frobenius eigenvalue attached to a source Xi divisor point. -/
def deningerArithmeticJetThetaEigen
    (rho : XiDivisorSupport) : ℂ :=
  1 / 2 + Complex.I * xiSpectralPointSupport rho

/-- Highest jet index retained by the divisor multiplicity at `rho`. -/
def deningerArithmeticJetIndexTop
    (rho : XiDivisorSupport) :
    DeningerArithmeticJetIndex rho :=
  ⟨xiSupportMultiplicity rho - 1,
    Nat.sub_lt (xiSupportMultiplicity_pos rho) Nat.one_pos⟩

@[simp] theorem deningerArithmeticJetIndexTop_val
    (rho : XiDivisorSupport) :
    (deningerArithmeticJetIndexTop rho).val =
      xiSupportMultiplicity rho - 1 :=
  rfl

/-- Distinct source divisor points have distinct affine Frobenius eigenvalues. -/
theorem deningerArithmeticJetThetaEigen_injective :
    Function.Injective deningerArithmeticJetThetaEigen := by
  intro rho tau h
  apply xiSpectralPointSupport_injective
  have hmul :
      Complex.I * xiSpectralPointSupport rho =
        Complex.I * xiSpectralPointSupport tau := by
    have hsub := congrArg (fun z : ℂ => z - 1 / 2) h
    simpa [deningerArithmeticJetThetaEigen] using hsub
  exact mul_left_cancel₀ Complex.I_ne_zero hmul

/-- Coordinate recurrence forced by a compact-open Frobenius eigenvector. -/
theorem deningerCompactOpenH1AllJets_eigen_coordinate
    {x : DeningerArithmeticCompactOpenH1}
    {rho : XiDivisorSupport}
    (hx :
      deningerCompactOpenTheta x =
        deningerArithmeticJetThetaEigen rho • x)
    (tau : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex tau) :
    deningerArithmeticJetThetaEigen tau *
          deningerCompactOpenH1AllJets x tau k +
        (k.val : ℂ) * Complex.I *
          deningerCompactOpenH1AllJets x tau
            (deningerArithmeticJetIndexPred tau k) =
      deningerArithmeticJetThetaEigen rho *
        deningerCompactOpenH1AllJets x tau k := by
  have h :=
    congrArg
      (fun y : DeningerArithmeticCompactOpenH1 =>
        deningerCompactOpenH1AllJets y tau k) hx
  change
    deningerCompactOpenH1AllJets
        (deningerCompactOpenTheta x) tau k =
      deningerCompactOpenH1AllJets
        (deningerArithmeticJetThetaEigen rho • x) tau k at h
  rw [deningerCompactOpenH1AllJets_theta] at h
  simpa [deningerArithmeticJetThetaEigen] using h

/-- Every source Frobenius eigenvector vanishes on jets over every other divisor point. -/
theorem deningerCompactOpenH1AllJets_eigen_off_support
    {x : DeningerArithmeticCompactOpenH1}
    {rho : XiDivisorSupport}
    (hx :
      deningerCompactOpenTheta x =
        deningerArithmeticJetThetaEigen rho • x)
    {tau : XiDivisorSupport}
    (htr : tau ≠ rho)
    (k : DeningerArithmeticJetIndex tau) :
    deningerCompactOpenH1AllJets x tau k = 0 := by
  have hne :
      deningerArithmeticJetThetaEigen tau ≠
        deningerArithmeticJetThetaEigen rho :=
    fun h => htr (deningerArithmeticJetThetaEigen_injective h)
  let m := xiSupportMultiplicity tau
  have hall :
      ∀ n (hn : n < m),
        deningerCompactOpenH1AllJets x tau
          (⟨n, hn⟩ : Fin m) = 0 := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hc :=
          deningerCompactOpenH1AllJets_eigen_coordinate hx tau
            (⟨0, hn⟩ : Fin m)
        have hmul :
            (deningerArithmeticJetThetaEigen tau -
                deningerArithmeticJetThetaEigen rho) *
              deningerCompactOpenH1AllJets x tau
                (⟨0, hn⟩ : Fin m) = 0 := by
          simp only [Nat.cast_zero, zero_mul] at hc
          linear_combination hc
        exact (mul_eq_zero.mp hmul).resolve_left
          (sub_ne_zero.mpr hne)
    | succ n ih =>
        intro hn
        have hnprev : n < m := lt_trans (Nat.lt_succ_self n) hn
        have hprev := ih hnprev
        have hc :=
          deningerCompactOpenH1AllJets_eigen_coordinate hx tau
            (⟨n + 1, hn⟩ : Fin m)
        have hpred :
            deningerArithmeticJetIndexPred tau
                (⟨n + 1, hn⟩ : Fin m) =
              (⟨n, hnprev⟩ : Fin m) := by
          apply Fin.ext
          simp [deningerArithmeticJetIndexPred]
        rw [hpred, hprev, mul_zero, add_zero] at hc
        have hmul :
            (deningerArithmeticJetThetaEigen tau -
                deningerArithmeticJetThetaEigen rho) *
              deningerCompactOpenH1AllJets x tau
                (⟨n + 1, hn⟩ : Fin m) = 0 := by
          linear_combination hc
        exact (mul_eq_zero.mp hmul).resolve_left
          (sub_ne_zero.mpr hne)
  exact hall k.val k.isLt

/-- At its own divisor point, an eigenvector has no jet below the highest retained order. -/
theorem deningerCompactOpenH1AllJets_eigen_below_top
    {x : DeningerArithmeticCompactOpenH1}
    {rho : XiDivisorSupport}
    (hx :
      deningerCompactOpenTheta x =
        deningerArithmeticJetThetaEigen rho • x)
    (n : ℕ)
    (hn : n + 1 < xiSupportMultiplicity rho) :
    deningerCompactOpenH1AllJets x rho
        (⟨n, lt_trans (Nat.lt_succ_self n) hn⟩ :
          DeningerArithmeticJetIndex rho) = 0 := by
  let k : DeningerArithmeticJetIndex rho :=
    ⟨n + 1, hn⟩
  have hc :=
    deningerCompactOpenH1AllJets_eigen_coordinate hx rho k
  have hpred :
      deningerArithmeticJetIndexPred rho k =
        (⟨n, lt_trans (Nat.lt_succ_self n) hn⟩ :
          DeningerArithmeticJetIndex rho) := by
    apply Fin.ext
    simp [k, deningerArithmeticJetIndexPred]
  rw [hpred] at hc
  have hmul :
      (((n + 1 : ℕ) : ℂ) * Complex.I) *
          deningerCompactOpenH1AllJets x rho
            (⟨n, lt_trans (Nat.lt_succ_self n) hn⟩ :
              DeningerArithmeticJetIndex rho) = 0 := by
    dsimp [k] at hc
    linear_combination hc
  exact (mul_eq_zero.mp hmul).resolve_left
    (mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      Complex.I_ne_zero)

/--
Every compact-open source Frobenius eigenvector is exactly a scalar multiple of the highest
jet basis vector at its source divisor point.
-/
theorem deningerCompactOpenH1AllJets_eigen_eq_top_basis
    {x : DeningerArithmeticCompactOpenH1}
    {rho : XiDivisorSupport}
    (hx :
      deningerCompactOpenTheta x =
        deningerArithmeticJetThetaEigen rho • x) :
    deningerCompactOpenH1AllJets x =
      (deningerCompactOpenH1AllJets x rho
          (deningerArithmeticJetIndexTop rho)) •
        deningerArithmeticJetBasisVector rho
          (deningerArithmeticJetIndexTop rho) := by
  funext tau k
  by_cases htr : tau = rho
  · subst tau
    by_cases hk : k = deningerArithmeticJetIndexTop rho
    · subst k
      simp [deningerArithmeticJetBasisVector, piBasisVector]
    · have hklt :
          k.val + 1 < xiSupportMultiplicity rho := by
        have hkval :
            k.val ≠ xiSupportMultiplicity rho - 1 := by
          intro hval
          apply hk
          apply Fin.ext
          simpa [deningerArithmeticJetIndexTop] using hval
        omega
      rw [deningerCompactOpenH1AllJets_eigen_below_top
        hx k.val hklt]
      simp [deningerArithmeticJetBasisVector, piBasisVector, hk]
  · rw [deningerCompactOpenH1AllJets_eigen_off_support
      hx htr k]
    simp [deningerArithmeticJetBasisVector, piBasisVector, htr]

/-- Canonical square-summable lift of the chosen source Frobenius eigenclass. -/
def deningerArithmeticJetSourceEigenvector
    (rho : XiDivisorSupport) :
    DeningerArithmeticJetHilbert :=
  lp.single 2
    (⟨rho, deningerArithmeticJetIndexTop rho⟩ :
      DeningerArithmeticJetCoordinate)
    (deningerCompactOpenH1AllJets
      (deningerCompactOpenThetaEigenvector rho) rho
      (deningerArithmeticJetIndexTop rho))

/-- The canonical square-summable eigenvector maps exactly to its chosen source eigenclass. -/
theorem deningerArithmeticJetSourceEigenvector_maps
    (rho : XiDivisorSupport) :
    deningerArithmeticJetHilbertToH1
        (deningerArithmeticJetSourceEigenvector rho) =
      deningerCompactOpenThetaEigenvector rho := by
  apply deningerCompactOpenH1AllJets_injective
  rw [deningerCompactOpenH1AllJets_eigen_eq_top_basis
    (deningerCompactOpenThetaEigenvector_eigen rho)]
  funext tau k
  rw [deningerCompactOpenH1AllJets_apply,
    deningerCompactOpenH1Jet_jetHilbertToH1
      (⟨tau, k⟩ : DeningerArithmeticJetCoordinate)
      (deningerArithmeticJetSourceEigenvector rho)]
  classical
  by_cases htr : tau = rho
  · subst tau
    by_cases hk : k = deningerArithmeticJetIndexTop rho
    · subst k
      simp [deningerArithmeticJetSourceEigenvector,
        deningerArithmeticJetBasisVector, piBasisVector,
        lp.single_apply]
    · have hcoord :
          (⟨rho, k⟩ : DeningerArithmeticJetCoordinate) ≠
            ⟨rho, deningerArithmeticJetIndexTop rho⟩ := by
        intro h
        apply hk
        apply Fin.ext
        exact congrArg
          (fun idx : DeningerArithmeticJetCoordinate =>
            idx.2.val) h
      simp [deningerArithmeticJetSourceEigenvector,
        deningerArithmeticJetBasisVector, piBasisVector,
        lp.single_apply, hk, hcoord]
  · have hcoord :
        (⟨tau, k⟩ : DeningerArithmeticJetCoordinate) ≠
          ⟨rho, deningerArithmeticJetIndexTop rho⟩ := by
      intro h
      exact htr
        (congrArg
          (fun idx : DeningerArithmeticJetCoordinate => idx.1) h)
    simp [deningerArithmeticJetSourceEigenvector,
      deningerArithmeticJetBasisVector, piBasisVector,
      lp.single_apply, htr, hcoord]

/-- The canonical square-summable lift is nonzero. -/
theorem deningerArithmeticJetSourceEigenvector_ne_zero
    (rho : XiDivisorSupport) :
    deningerArithmeticJetSourceEigenvector rho ≠ 0 := by
  intro hzero
  have hmap := deningerArithmeticJetSourceEigenvector_maps rho
  rw [hzero, map_zero] at hmap
  exact deningerCompactOpenThetaEigenvector_ne_zero rho hmap.symm

/-- The canonical lift belongs to the maximal closed source Frobenius domain. -/
theorem deningerArithmeticJetSourceEigenvector_mem_thetaDomain
    (rho : XiDivisorSupport) :
    deningerArithmeticJetSourceEigenvector rho ∈
      deningerArithmeticJetClosedTheta.domain := by
  unfold deningerArithmeticJetSourceEigenvector
  have hb :=
    deningerArithmeticJetClosedTheta.domain.smul_mem
      (deningerCompactOpenH1AllJets
        (deningerCompactOpenThetaEigenvector rho) rho
        (deningerArithmeticJetIndexTop rho))
      (deningerArithmeticJetBasis_mem_thetaDomain
        (⟨rho, deningerArithmeticJetIndexTop rho⟩ :
          DeningerArithmeticJetCoordinate))
  simpa only [← lp.single_smul, smul_eq_mul, mul_one] using hb

/-- Canonical source eigenclass as an element of the closed Frobenius domain. -/
def deningerArithmeticJetClosedThetaEigenvector
    (rho : XiDivisorSupport) :
    deningerArithmeticJetClosedTheta.domain :=
  ⟨deningerArithmeticJetSourceEigenvector rho,
    deningerArithmeticJetSourceEigenvector_mem_thetaDomain rho⟩

/-- Every source Xi divisor point survives as a genuine eigenvector of the closed jet generator. -/
theorem deningerArithmeticJetClosedTheta_eigenvector
    (rho : XiDivisorSupport) :
    deningerArithmeticJetClosedTheta
        (deningerArithmeticJetClosedThetaEigenvector rho) =
      deningerArithmeticJetThetaEigen rho •
        (deningerArithmeticJetClosedThetaEigenvector rho :
          DeningerArithmeticJetHilbert) := by
  apply deningerArithmeticJetHilbertToH1_injective
  rw [deningerArithmeticJetClosedTheta_distribution]
  change
    deningerCompactOpenTheta
        (deningerArithmeticJetHilbertToH1
          (deningerArithmeticJetSourceEigenvector rho)) =
      deningerArithmeticJetHilbertToH1
        (deningerArithmeticJetThetaEigen rho •
          deningerArithmeticJetSourceEigenvector rho)
  rw [deningerArithmeticJetSourceEigenvector_maps,
    deningerCompactOpenThetaEigenvector_eigen,
    map_smul,
    deningerArithmeticJetSourceEigenvector_maps]
  rfl

end

end RHTower
