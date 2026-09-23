import GaloisForLFunctions.HTGeometry.DbarPolydiscSolve

/-!
# The Dolbeault–Grothendieck lemma on a product domain

The Dolbeault induction never uses that the factors of the domain are discs: it uses only that the
domain is a product of open subsets of the plane, so that moving one coordinate inside its own
factor stays inside the domain, and that a cutoff in the distinguished coordinate is available.
Both hold for any product of open plane domains — in particular for a polyannulus, which is the
domain the exhaustion of `(ℂ^×)^r` needs.

The induction shrinks the domain once per coordinate, so it is run along a decreasing chain of
product domains, with a cutoff pair supplied for each consecutive pair of the chain.

* `HTGeometry.productDomain` : the product of a family of plane domains.
* `HTGeometry.dbar_product_step_smooth` : the induction step.
* `HTGeometry.dbar_product_solve` : **the Dolbeault–Grothendieck lemma on a product domain.**
-/

namespace HTGeometry

open Complex

section ProductDomain

variable {n : ℕ}

/-- The product of a family of plane domains. -/
def productDomain (D : Fin n → Set ℂ) : Set (Fin n → ℂ) := {z | ∀ i, z i ∈ D i}

theorem mem_productDomain {D : Fin n → Set ℂ} {z : Fin n → ℂ} :
    z ∈ productDomain D ↔ ∀ i, z i ∈ D i := Iff.rfl

theorem productDomain_mono {D D' : Fin n → Set ℂ} (h : ∀ i, D' i ⊆ D i) :
    productDomain D' ⊆ productDomain D := fun _ hz i => h i (hz i)

theorem isOpen_productDomain {D : Fin n → Set ℂ} (h : ∀ i, IsOpen (D i)) :
    IsOpen (productDomain D) := by
  have heq : productDomain D = ⋂ i : Fin n, (fun z : Fin n → ℂ => z i) ⁻¹' D i := by
    ext z
    simp [productDomain, Set.mem_iInter]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => (h i).preimage (continuous_apply i)

/-- **A product domain is closed under moving one coordinate inside its own factor.** -/
theorem update_mem_productDomain {D : Fin n → Set ℂ} {z : Fin n → ℂ} (hz : z ∈ productDomain D)
    {k : Fin n} {t : ℂ} (ht : t ∈ D k) : Function.update z k t ∈ productDomain D := by
  intro i
  by_cases hik : i = k
  · subst hik
    rwa [Function.update_self]
  · rw [Function.update_of_ne hik]
    exact hz i

end ProductDomain

section ProductStep

variable {n : ℕ}

/-- **The Dolbeault induction step on a product domain.**  The cutoff is a function of the `k`-th
coordinate alone times one that does not depend on the domain; the product is compactly supported,
so the coordinatewise Cauchy transform is smooth, while the second factor is invisible to `∂̄_j`
along every `k`-line meeting the domain. -/
theorem dbar_product_step_smooth {f : Fin n → (Fin n → ℂ) → ℂ} {D D' : Fin n → Set ℂ}
    {k : Fin n} (hD : ∀ i, D' i ⊆ D i) (hopen : ∀ i, IsOpen (D i))
    (chi : ℂ → ℝ) (psi : (Fin n → ℂ) → ℝ)
    (hchi : ∀ t : ℂ, chi t ≠ 0 → t ∈ D k)
    (hchione : ∀ z ∈ productDomain D', chi (z k) = 1)
    (hpsione : ∀ z ∈ productDomain D, psi z = 1)
    (hCG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)))
    (hcs : HasCompactSupport (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)))
    (hclosed : ∀ j : Fin n, ∀ z ∈ productDomain D, dzbarAt (f k) j z = dzbarAt (f j) k z) :
    ∃ U : (Fin n → ℂ) → ℂ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
      (∀ z ∈ productDomain D', dzbarAt U k z = f k z) ∧
      ∀ j : Fin n, j ≠ k → (∀ y ∈ productDomain D, f j y = 0) →
        ∀ z ∈ productDomain D', dzbarAt U j z = 0 := by
  set F : (Fin n → ℂ) → ℂ :=
    fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x) with hF
  have hC1 : ContDiff ℝ 1 F := hCG.of_le (by exact_mod_cast le_top)
  obtain ⟨S, hS, hgS⟩ := exists_slab_of_hasCompactSupport hcs k
  obtain ⟨Sd, hSd, hdS⟩ := exists_slab_of_hasCompactSupport (hcs.fderiv ℝ) k
  obtain ⟨M, hM⟩ :=
    (hcs.fderiv ℝ).exists_bound_of_continuous (hC1.continuous_fderiv one_ne_zero)
  obtain ⟨M₀, hM₀⟩ := hcs.exists_bound_of_continuous hC1.continuous
  set T : ℝ := max S Sd with hT
  have hgT : ∀ x : Fin n → ℂ, T < ‖x k‖ → F x = 0 :=
    fun x hx => hgS x (lt_of_le_of_lt (le_max_left _ _) hx)
  have hdT : ∀ x : Fin n → ℂ, T < ‖x k‖ → fderiv ℝ F x = 0 :=
    fun x hx => hdS x (lt_of_le_of_lt (le_max_right _ _) hx)
  refine ⟨dbarSliceSolution F k, contDiff_infty_dbarSliceSolution F k hCG hcs, ?_, ?_⟩
  · intro z hz
    rw [dzbarAt_dbarSliceSolution_of_slab hC1 hgT z, hF]
    show (chi (z k) : ℝ) • ((psi z : ℝ) • f k z) = f k z
    rw [hchione z hz, hpsione z (productDomain_mono hD hz), one_smul, one_smul]
  · intro j hjk hfj z hz
    refine dzbarAt_dbarSliceSolution_eq_zero hjk hC1 hgT hdT hM hM₀ z ?_
    intro t
    have hslice : dzbarAt F j (Function.update z k t)
        = (chi t : ℝ) • dzbarAt (fun x : Fin n → ℂ => (psi x : ℝ) • f k x) j
            (Function.update z k t) := by
      rw [hF, dzbarAt_slabCutoff_smul hjk chi, Function.update_self]
    rw [hslice]
    by_cases ht : chi t = 0
    · rw [ht, zero_smul]
    · have hmem : Function.update z k t ∈ productDomain D :=
        update_mem_productDomain (productDomain_mono hD hz) (hchi t ht)
      have hloc : dzbarAt (fun x : Fin n → ℂ => (psi x : ℝ) • f k x) j (Function.update z k t)
          = dzbarAt (f k) j (Function.update z k t) := by
        refine dzbarAt_congr_of_eventuallyEq ?_
        refine Filter.eventually_of_mem ((isOpen_productDomain hopen).mem_nhds hmem)
          (fun y hy => ?_)
        show (psi y : ℝ) • f k y = f k y
        rw [hpsione y hy, one_smul]
      rw [hloc, hclosed j _ hmem]
      have hzero : dzbarAt (f j) k (Function.update z k t) = 0 := by
        refine dzbarAt_eq_zero_of_eventually_zero ?_
        exact Filter.eventually_of_mem ((isOpen_productDomain hopen).mem_nhds hmem)
          (fun y hy => hfj y hy)
      rw [hzero, smul_zero]

end ProductStep

section ProductRecursion

variable {n : ℕ}

/-- **The Dolbeault induction along a chain of product domains.**  Each step solves in one
direction and moves one link down the chain; the residue is again smooth and `∂̄`-closed. -/
theorem dbar_product_solve_aux (Dom : ℕ → Fin n → Set ℂ)
    (hopen : ∀ o i, IsOpen (Dom o i))
    (hmono : ∀ o i, Dom (o + 1) i ⊆ Dom o i)
    (hcut : ∀ (o : ℕ) (k : Fin n), ∃ chi : ℂ → ℝ, ∃ psi : (Fin n → ℂ) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi ∧ HasCompactSupport psi ∧
      (∀ t : ℂ, chi t ≠ 0 → t ∈ Dom o k) ∧
      (∀ z ∈ productDomain (Dom (o + 1)), chi (z k) = 1) ∧
      (∀ z ∈ productDomain (Dom o), psi z = 1)) :
    ∀ (m o : ℕ) (f : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j)) →
      (∀ j j' : Fin n, ∀ z ∈ productDomain (Dom o), dzbarAt (f j) j' z = dzbarAt (f j') j z) →
      (∀ j : Fin n, m ≤ (j : ℕ) → ∀ z ∈ productDomain (Dom o), f j z = 0) →
      ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
        ∀ j : Fin n, ∀ z ∈ productDomain (Dom (o + m)), dzbarAt u j z = f j z := by
  intro m
  induction m with
  | zero =>
      intro o f _ _ hvan
      refine ⟨fun _ => 0, contDiff_const, fun j z hz => ?_⟩
      rw [dzbarAt_zero]
      exact (hvan j (Nat.zero_le _) z hz).symm
  | succ m ih =>
      intro o f hCf hclosed hvan
      have hstepmono : productDomain (Dom (o + (m + 1))) ⊆ productDomain (Dom (o + m)) := by
        have hidx : o + (m + 1) = (o + m) + 1 := by omega
        rw [hidx]
        exact productDomain_mono fun i => hmono (o + m) i
      by_cases hmn : n ≤ m
      · obtain ⟨u, hCu, hu⟩ :=
          ih o f hCf hclosed fun j hj => absurd hj (by have := j.isLt; omega)
        exact ⟨u, hCu, fun j z hz => hu j z (hstepmono hz)⟩
      · push_neg at hmn
        set k : Fin n := ⟨m, hmn⟩ with hk
        obtain ⟨chi, psi, hCchi, hCpsi, hcspsi, hchi, hchione, hpsione⟩ := hcut o k
        have hCG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)) :=
          (hCchi.comp (contDiff_apply ℝ ℂ k)).smul (hCpsi.smul (hCf k))
        have hcs : HasCompactSupport
            (fun x : Fin n → ℂ => (chi (x k) : ℝ) • ((psi x : ℝ) • f k x)) := by
          refine hcspsi.mono fun x hx => ?_
          by_contra hzero
          simp only [Function.mem_support, not_not] at hzero
          exact hx (by simp [hzero])
        obtain ⟨U, hCU, hUk, hUj⟩ :=
          dbar_product_step_smooth (f := f) (D := Dom o) (D' := Dom (o + 1)) (k := k)
            (fun i => hmono o i) (hopen o) chi psi hchi hchione hpsione hCG hcs
            (fun j z hz => hclosed k j z hz)
        have hdU : Differentiable ℝ U := hCU.differentiable (by simp)
        have hCU2 : ContDiff ℝ 2 U := hCU.of_le (by decide)
        have hCdU : ∀ j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dzbarAt U j) :=
          fun j => contDiff_infty_dzbarAt hCU j
        have hddU : ∀ j : Fin n, Differentiable ℝ (dzbarAt U j) :=
          fun j => (hCdU j).differentiable (by simp)
        have hdf : ∀ j : Fin n, Differentiable ℝ (f j) := fun j => (hCf j).differentiable (by simp)
        have hsub : productDomain (Dom (o + 1)) ⊆ productDomain (Dom o) :=
          productDomain_mono fun i => hmono o i
        set g : Fin n → (Fin n → ℂ) → ℂ := fun j z => f j z - dzbarAt U j z with hgdef
        have hCg : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g j) :=
          fun j => (hCf j).sub (hCdU j)
        have hclosedg : ∀ j j' : Fin n, ∀ z ∈ productDomain (Dom (o + 1)),
            dzbarAt (g j) j' z = dzbarAt (g j') j z := by
          intro j j' z hz
          have h1 : dzbarAt (g j) j' z = dzbarAt (f j) j' z - dzbarAt (dzbarAt U j) j' z :=
            dzbarAt_sub (hdf j) (hddU j) j' z
          have h2 : dzbarAt (g j') j z = dzbarAt (f j') j z - dzbarAt (dzbarAt U j') j z :=
            dzbarAt_sub (hdf j') (hddU j') j z
          rw [h1, h2, hclosed j j' z (hsub hz), dzbarAt_comm hCU2 j' j z]
        have hvang : ∀ j : Fin n, m ≤ (j : ℕ) →
            ∀ z ∈ productDomain (Dom (o + 1)), g j z = 0 := by
          intro j hj z hz
          rcases eq_or_lt_of_le hj with heq | hlt
          · have hjk : j = k := Fin.ext heq.symm
            subst hjk
            show f k z - dzbarAt U k z = 0
            rw [hUk z hz]
            ring
          · have hjne : j ≠ k := by
              intro h
              rw [h] at hlt
              exact absurd hlt (by simp [hk])
            have hfj : ∀ y ∈ productDomain (Dom o), f j y = 0 := hvan j (by omega)
            show f j z - dzbarAt U j z = 0
            rw [hfj z (hsub hz), hUj j hjne hfj z hz]
            ring
        obtain ⟨v, hCv, hv⟩ := ih (o + 1) g hCg hclosedg hvang
        have hidx : o + 1 + m = o + (m + 1) := by omega
        rw [hidx] at hv
        have hdv : Differentiable ℝ v := hCv.differentiable (by simp)
        refine ⟨fun x => U x + v x, hCU.add hCv, ?_⟩
        exact dzbarAt_add_solution hdU hdv fun j z hz => hv j z hz

/-- **The Dolbeault–Grothendieck lemma on a product domain.**  A smooth `∂̄`-closed datum on the
first domain of a decreasing chain of product domains, each pair of which carries a cutoff, has a
smooth primitive on the `n`-th domain of the chain. -/
theorem dbar_product_solve (Dom : ℕ → Fin n → Set ℂ)
    (hopen : ∀ o i, IsOpen (Dom o i))
    (hmono : ∀ o i, Dom (o + 1) i ⊆ Dom o i)
    (hcut : ∀ (o : ℕ) (k : Fin n), ∃ chi : ℂ → ℝ, ∃ psi : (Fin n → ℂ) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi ∧ HasCompactSupport psi ∧
      (∀ t : ℂ, chi t ≠ 0 → t ∈ Dom o k) ∧
      (∀ z ∈ productDomain (Dom (o + 1)), chi (z k) = 1) ∧
      (∀ z ∈ productDomain (Dom o), psi z = 1))
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hCf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hclosed : ∀ j j' : Fin n, ∀ z ∈ productDomain (Dom 0),
      dzbarAt (f j) j' z = dzbarAt (f j') j z) :
    ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
      ∀ j : Fin n, ∀ z ∈ productDomain (Dom n), dzbarAt u j z = f j z := by
  have h := dbar_product_solve_aux Dom hopen hmono hcut n 0 f hCf hclosed
    fun j hj => absurd hj (by have := j.isLt; omega)
  rwa [Nat.zero_add] at h

end ProductRecursion

section Annulus

variable {n : ℕ}

/-- The open annulus of inner radius `a` and outer radius `b`. -/
def annulus (a b : ℝ) : Set ℂ := {t : ℂ | a < ‖t‖ ∧ ‖t‖ < b}

theorem mem_annulus {a b : ℝ} {t : ℂ} : t ∈ annulus a b ↔ a < ‖t‖ ∧ ‖t‖ < b := Iff.rfl

theorem isOpen_annulus (a b : ℝ) : IsOpen (annulus a b) := by
  have heq : annulus a b = (fun t : ℂ => ‖t‖) ⁻¹' (Set.Ioo a b) := by
    ext t
    simp [annulus, Set.mem_Ioo]
  rw [heq]
  exact isOpen_Ioo.preimage continuous_norm

theorem annulus_mono {a a' b' b : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    annulus a' b' ⊆ annulus a b :=
  fun _ ht => ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩

/-- The squared norm on the plane is smooth. -/
theorem contDiff_normSq_complex :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℂ => ‖t‖ ^ (2 : ℕ)) := by
  have h : (fun t : ℂ => ‖t‖ ^ (2 : ℕ)) = fun t : ℂ => t.re ^ (2 : ℕ) + t.im ^ (2 : ℕ) := by
    funext t
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg t), Complex.normSq_apply]
    ring
  rw [h]
  exact ((Complex.reCLM.contDiff).pow 2).add ((Complex.imCLM.contDiff).pow 2)

/-- **A smooth cutoff adapted to a pair of nested annuli.**  It is a bump in the squared radius,
which is a polynomial in the real coordinates and so smooth everywhere, including at the origin
where the radius itself is not. -/
theorem exists_annulus_cutoff {a a' b' b : ℝ} (ha : 0 ≤ a) (haa' : a < a') (ha'b' : a' < b')
    (hb'b : b' < b) :
    ∃ chi : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi ∧
      (∀ t : ℂ, chi t ≠ 0 → t ∈ annulus a b) ∧ (∀ t ∈ annulus a' b', chi t = 1) := by
  have ha'0 : 0 < a' := lt_of_le_of_lt ha haa'
  have hb'0 : 0 < b' := lt_trans ha'0 ha'b'
  have hb0 : 0 < b := lt_trans hb'0 hb'b
  set c : ℝ := (a' ^ (2 : ℕ) + b' ^ (2 : ℕ)) / 2 with hc
  set rIn : ℝ := (b' ^ (2 : ℕ) - a' ^ (2 : ℕ)) / 2 with hrIn
  have hrInpos : 0 < rIn := by
    rw [hrIn]
    nlinarith
  set rOut : ℝ := min (c - a ^ (2 : ℕ)) (b ^ (2 : ℕ) - c) with hrOut
  have hca : a ^ (2 : ℕ) < c := by
    rw [hc]
    nlinarith
  have hcb : c < b ^ (2 : ℕ) := by
    rw [hc]
    nlinarith
  have hrOutpos : rIn < rOut := by
    rw [hrOut, lt_min_iff]
    constructor
    · rw [hrIn, hc]
      nlinarith
    · rw [hrIn, hc]
      nlinarith
  let bump : ContDiffBump c := ⟨rIn, rOut, hrInpos, hrOutpos⟩
  refine ⟨fun t => bump (‖t‖ ^ (2 : ℕ)), bump.contDiff.comp contDiff_normSq_complex, ?_, ?_⟩
  · intro t ht
    have hsupp : ‖t‖ ^ (2 : ℕ) ∈ Function.support (bump : ℝ → ℝ) := ht
    rw [bump.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hsupp
    have h1 : a ^ (2 : ℕ) < ‖t‖ ^ (2 : ℕ) := by
      have := hsupp.1
      have hle : rOut ≤ c - a ^ (2 : ℕ) := min_le_left _ _
      linarith
    have h2 : ‖t‖ ^ (2 : ℕ) < b ^ (2 : ℕ) := by
      have := hsupp.2
      have hle : rOut ≤ b ^ (2 : ℕ) - c := min_le_right _ _
      linarith
    refine ⟨?_, ?_⟩
    · nlinarith [norm_nonneg t]
    · nlinarith [norm_nonneg t]
  · intro t ht
    refine bump.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    have h1 : a' ^ (2 : ℕ) < ‖t‖ ^ (2 : ℕ) := by nlinarith [ht.1, ha'0]
    have h2 : ‖t‖ ^ (2 : ℕ) < b' ^ (2 : ℕ) := by nlinarith [ht.2, norm_nonneg t, hb'0]
    have hbin : bump.rIn = rIn := rfl
    rw [hbin, hrIn, hc]
    constructor
    · nlinarith
    · nlinarith

/-- **A smooth compactly supported function equal to one on a bounded product domain.** -/
theorem exists_bounded_bump {D : Fin n → Set ℂ} {R : ℝ} (hRpos : 0 < R)
    (hbdd : ∀ (z : Fin n → ℂ), z ∈ productDomain D → ∀ i, ‖z i‖ ≤ R) :
    ∃ psi : (Fin n → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi ∧
      HasCompactSupport psi ∧ ∀ z ∈ productDomain D, psi z = 1 := by
  let bump : ContDiffBump (0 : Fin n → ℂ) := ⟨R, R + 1, hRpos, by linarith⟩
  refine ⟨(bump : (Fin n → ℂ) → ℝ), bump.contDiff, bump.hasCompactSupport, fun z hz => ?_⟩
  refine bump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_pi_le_iff hRpos.le]
  intro i
  rw [Complex.dist_eq]
  simpa using hbdd z hz i

end Annulus

section Polyannulus

variable {n : ℕ}

/-- The chain of polyannuli interpolating between an outer and an inner pair of radii. -/
noncomputable def annulusChainIn (a a' : Fin n → ℝ) (o : ℕ) (i : Fin n) : ℝ :=
  a i + (a' i - a i) * (1 - (1 / 2 : ℝ) ^ o)

/-- The outer radii of the chain. -/
noncomputable def annulusChainOut (b b' : Fin n → ℝ) (o : ℕ) (i : Fin n) : ℝ :=
  b i - (b i - b' i) * (1 - (1 / 2 : ℝ) ^ o)

/-- **The Dolbeault–Grothendieck lemma on a polyannulus.**  A smooth `∂̄`-closed datum on the
polyannulus of radii `(a, b)` has a smooth primitive on every strictly smaller polyannulus. -/
theorem dbar_polyannulus_solve {a a' b' b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (haa' : ∀ i, a i < a' i) (ha'b' : ∀ i, a' i < b' i)
    (hb'b : ∀ i, b' i < b i)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hCf : ∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j))
    (hclosed : ∀ j j' : Fin n, ∀ z ∈ productDomain (fun i => annulus (a i) (b i)),
      dzbarAt (f j) j' z = dzbarAt (f j') j z) :
    ∃ u : (Fin n → ℂ) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u ∧
      ∀ j : Fin n, ∀ z ∈ productDomain (fun i => annulus (a' i) (b' i)),
        dzbarAt u j z = f j z := by
  classical
  set A : ℕ → Fin n → ℝ := annulusChainIn a a' with hA
  set B : ℕ → Fin n → ℝ := annulusChainOut b b' with hB
  set Dom : ℕ → Fin n → Set ℂ := fun o i => annulus (A o i) (B o i) with hDom
  have hhalf : ∀ o : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ o := fun o => by positivity
  have hhalfle : ∀ o : ℕ, (1 / 2 : ℝ) ^ o ≤ 1 := fun o => pow_le_one₀ (by norm_num) (by norm_num)
  have hhalfstep : ∀ o : ℕ, (1 / 2 : ℝ) ^ (o + 1) < (1 / 2 : ℝ) ^ o := fun o => by
    rw [pow_succ]
    nlinarith [hhalf o]
  have hAlt : ∀ (o : ℕ) (i : Fin n), A o i < a' i := by
    intro o i
    simp only [hA, annulusChainIn]
    nlinarith [haa' i, hhalf o]
  have hBgt : ∀ (o : ℕ) (i : Fin n), b' i < B o i := by
    intro o i
    simp only [hB, annulusChainOut]
    nlinarith [hb'b i, hhalf o]
  have hAge : ∀ (o : ℕ) (i : Fin n), a i ≤ A o i := by
    intro o i
    simp only [hA, annulusChainIn]
    nlinarith [haa' i, hhalfle o]
  have hBle : ∀ (o : ℕ) (i : Fin n), B o i ≤ b i := by
    intro o i
    simp only [hB, annulusChainOut]
    nlinarith [hb'b i, hhalfle o]
  have hAstep : ∀ (o : ℕ) (i : Fin n), A o i < A (o + 1) i := by
    intro o i
    simp only [hA, annulusChainIn]
    nlinarith [haa' i, hhalfstep o]
  have hBstep : ∀ (o : ℕ) (i : Fin n), B (o + 1) i < B o i := by
    intro o i
    simp only [hB, annulusChainOut]
    nlinarith [hb'b i, hhalfstep o]
  have hAnn : ∀ (o : ℕ) (i : Fin n), 0 ≤ A o i := fun o i => le_trans (ha i) (hAge o i)
  have hopen : ∀ o i, IsOpen (Dom o i) := fun o i => isOpen_annulus _ _
  have hmono : ∀ o i, Dom (o + 1) i ⊆ Dom o i := fun o i =>
    annulus_mono (hAstep o i).le (hBstep o i).le
  set R : ℝ := 1 + ∑ i, |b i| with hR
  have hRpos : 0 < R := by
    rw [hR]
    positivity
  have hbR : ∀ i : Fin n, b i ≤ R := by
    intro i
    have h1 : |b i| ≤ ∑ i', |b i'| :=
      Finset.single_le_sum (f := fun i' => |b i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : b i ≤ |b i| := le_abs_self _
    rw [hR]
    linarith
  have hABstep : ∀ (o : ℕ) (i : Fin n), A o i < B o i := fun o i => by
    have h1 := hAlt o i
    have h2 := ha'b' i
    have h3 := hBgt o i
    linarith
  have hbounded : ∀ (o : ℕ) (z : Fin n → ℂ), z ∈ productDomain (Dom o) → ∀ i, ‖z i‖ ≤ R := by
    intro o z hz i
    exact le_of_lt (lt_of_lt_of_le (hz i).2 (le_trans (hBle o i) (hbR i)))
  have hcut : ∀ (o : ℕ) (k : Fin n), ∃ chi : ℂ → ℝ, ∃ psi : (Fin n → ℂ) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) chi ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psi ∧ HasCompactSupport psi ∧
      (∀ t : ℂ, chi t ≠ 0 → t ∈ Dom o k) ∧
      (∀ z ∈ productDomain (Dom (o + 1)), chi (z k) = 1) ∧
      (∀ z ∈ productDomain (Dom o), psi z = 1) := by
    intro o k
    obtain ⟨chi, hCchi, hchisupp, hchione⟩ :=
      exists_annulus_cutoff (a := A o k) (a' := A (o + 1) k) (b' := B (o + 1) k) (b := B o k)
        (hAnn o k) (hAstep o k) (hABstep (o + 1) k) (hBstep o k)
    obtain ⟨psi, hCpsi, hcspsi, hpsione⟩ :=
      exists_bounded_bump (D := Dom o) (R := R) hRpos (hbounded o)
    exact ⟨chi, psi, hCchi, hCpsi, hcspsi, hchisupp, fun z hz => hchione (z k) (hz k), hpsione⟩
  have hDom0 : Dom 0 = fun i => annulus (a i) (b i) := by
    funext i
    simp only [hDom, hA, hB, annulusChainIn, annulusChainOut, pow_zero]
    norm_num
  have hclosed' : ∀ j j' : Fin n, ∀ z ∈ productDomain (Dom 0),
      dzbarAt (f j) j' z = dzbarAt (f j') j z := by
    rw [hDom0]
    exact hclosed
  obtain ⟨u, hCu, hu⟩ := dbar_product_solve Dom hopen hmono hcut hCf hclosed'
  refine ⟨u, hCu, fun j z hz => hu j z fun i => ?_⟩
  exact ⟨lt_trans (hAlt n i) (hz i).1, lt_trans (hz i).2 (hBgt n i)⟩

end Polyannulus

end HTGeometry
