import GaloisForLFunctions.RHTower.DeningerArithmeticJetHilbertRigging

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
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem h1mem]
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

/-- Maximal `ell^2` domain of source jet Frobenius. -/
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

end

end RHTower
