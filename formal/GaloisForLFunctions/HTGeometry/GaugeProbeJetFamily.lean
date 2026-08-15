import GaloisForLFunctions.HTGeometry.GaugeCarrierJets

/-!
# A polynomial probe of a gauged source is a submersion onto jets

Perturbing the exponent of a gauged source `W·exp(g)` by a finite-dimensional family of polynomials
moves its finite jet packet at finitely many nodes.  The derivative of that motion factors into
three maps: the jet map of the probe family, the exponential jet map, whose Jacobian is triangular
with diagonal the nonvanishing value, and multiplication by the source, whose Leibniz matrix is
triangular with diagonal `W` at the node.  The last two are invertible wherever `W` does not vanish,
so the probe is a submersion onto the jets exactly when its own jet map is onto.

The probe family is packaged so that the same argument serves an unconstrained coefficient window
and a symmetry- or passport-constrained family.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [Fintype X]

/-! ### Probe families -/

/-- A finite-dimensional real family of polynomial perturbations of an exponent, together with its
jet map at an arbitrary node family. -/
structure GaugeProbe (X : Type*) [Fintype X] (m D : ℕ) where
  /-- The polynomial attached to a coefficient vector. -/
  poly : (Fin D → ℂ) → Polynomial ℂ
  /-- Its jets at a family of nodes, as a real-linear map of the coefficient vector. -/
  jet : (X → ℂ) → ((Fin D → ℂ) →L[ℝ] (X → Fin m → ℂ))
  /-- The linear map really is the jet packet of the polynomial. -/
  jet_eq : ∀ (ν : X → ℂ) (c : Fin D → ℂ) (x : X),
    jet ν c x = gaugeJetVec m (fun w => Polynomial.eval w (poly c)) (ν x)
  /-- The zero coefficient vector gives no perturbation. -/
  poly_zero : poly 0 = 0
  /-- Every jet coordinate is jointly smooth in the coefficients and the node. -/
  polyJet_contDiff : ∀ k : ℕ, ContDiff ℝ ⊤ (fun q : (Fin D → ℂ) × ℂ =>
    (Polynomial.derivative^[k] (poly q.1)).eval q.2)

/-! ### The window probe -/

/-- The jets of a window polynomial at a family of nodes. -/
def windowProbeJetLin (m N D : ℕ) (ν : X → ℂ) : (Fin D → ℂ) →ₗ[ℂ] (X → Fin m → ℂ) :=
  LinearMap.pi fun x => LinearMap.pi fun k : Fin m =>
    (Polynomial.leval (ν x)).comp
      ((Polynomial.derivative (R := ℂ) ^ ((k : ℕ))).comp (windowLin N D))

omit [Fintype X] in
theorem windowProbeJetLin_apply (m N D : ℕ) (ν : X → ℂ) (c : Fin D → ℂ) (x : X) (k : Fin m) :
    windowProbeJetLin m N D ν c x k
      = (Polynomial.derivative^[(k : ℕ)] (windowLin N D c)).eval (ν x) := by
  rw [windowProbeJetLin, LinearMap.pi_apply, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, Module.End.pow_apply]
  rfl

omit [Fintype X] in
theorem windowProbeJetLin_eq_gaugeJetVec (m N D : ℕ) (ν : X → ℂ) (c : Fin D → ℂ) (x : X) :
    windowProbeJetLin m N D ν c x
      = gaugeJetVec m (fun w => Polynomial.eval w (windowLin N D c)) (ν x) := by
  funext k
  rw [windowProbeJetLin_apply, gaugeJetVec, iteratedDeriv_polynomial_eval]

theorem iterate_derivative_eq_pow (k : ℕ) (P : Polynomial ℂ) :
    Polynomial.derivative^[k] P = ((Polynomial.derivative (R := ℂ)) ^ k) P :=
  (Module.End.pow_apply _ _ _).symm

/-- The jets of a window polynomial expand linearly in the coefficient vector. -/
theorem windowLin_iterate_derivative_eval (N D k : ℕ) (c : Fin D → ℂ) (ζ : ℂ) :
    (Polynomial.derivative^[k] (windowLin N D c)).eval ζ
      = ∑ i : Fin D, c i *
        (Polynomial.derivative^[k] (Polynomial.monomial (N + (i : ℕ)) (1 : ℂ))).eval ζ := by
  rw [iterate_derivative_eq_pow, windowLin_apply, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmon : (Polynomial.monomial (N + (i : ℕ)) (c i) : Polynomial ℂ)
      = c i • Polynomial.monomial (N + (i : ℕ)) (1 : ℂ) := by
    rw [Polynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hmon, map_smul, Polynomial.eval_smul, iterate_derivative_eq_pow, smul_eq_mul]

theorem contDiff_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) : ContDiff ℝ ⊤ f := by
  have hC : ContDiff ℂ ⊤ f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hf.differentiableOn.analyticOnNhd isOpen_univ) x (Set.mem_univ x)).contDiffAt
  exact hC.restrict_scalars ℝ

/-- The unconstrained coefficient window, as a probe family. -/
def windowProbe (X : Type*) [Fintype X] (m N D : ℕ) : GaugeProbe X m D where
  poly c := windowLin N D c
  jet ν := (LinearMap.toContinuousLinearMap (windowProbeJetLin m N D ν)).restrictScalars ℝ
  jet_eq ν c x := windowProbeJetLin_eq_gaugeJetVec m N D ν c x
  poly_zero := map_zero _
  polyJet_contDiff k := by
    have hfun : (fun q : (Fin D → ℂ) × ℂ =>
          (Polynomial.derivative^[k] (windowLin N D q.1)).eval q.2)
        = fun q : (Fin D → ℂ) × ℂ => ∑ i : Fin D, q.1 i *
            (Polynomial.derivative^[k] (Polynomial.monomial (N + (i : ℕ)) (1 : ℂ))).eval q.2 := by
      funext q
      rw [windowLin_iterate_derivative_eval]
    rw [hfun]
    refine ContDiff.sum fun i _ => ?_
    exact ((contDiff_apply ℝ ℂ i).comp contDiff_fst).mul
      ((contDiff_of_entire (Polynomial.differentiable _)).comp contDiff_snd)

/-- **The window jet map at distinct nonzero nodes is onto every jet target.** -/
theorem surjective_windowProbe_jet [DecidableEq X] (m N : ℕ) {ν : X → ℂ}
    (hinj : Function.Injective ν) (hne : ∀ x, ν x ≠ 0) :
    Function.Surjective ((windowProbe X m N (Fintype.card X * m)).jet ν) := by
  classical
  set e := Fintype.equivFin X with he
  set y : Fin (Fintype.card X) → ℂ := fun a => ν (e.symm a) with hy
  have hyinj : Function.Injective y := fun a b hab => e.symm.injective (hinj hab)
  have hy0 : ∀ a, y a ≠ 0 := fun a => hne _
  intro target
  obtain ⟨c, hc⟩ := windowJetMap_surjective (x := y) hyinj hy0 m N
    (fun p : Fin (Fintype.card X) × Fin m => target (e.symm p.1) p.2)
  refine ⟨c, ?_⟩
  funext x k
  have hval := congrFun hc (e x, k)
  rw [windowJetMap_apply] at hval
  show windowProbeJetLin m N (Fintype.card X * m) ν c x k = target x k
  rw [windowProbeJetLin_apply]
  have hnode : y (e x) = ν x := by rw [hy]; simp
  rw [← hnode, hval]
  simp

/-! ### Multiplication by the source on jets -/

/-- Multiplication by a fixed source on the jets at each node. -/
def leibnizBlockLin (m : ℕ) (Wj : X → ℕ → ℂ) :
    (X → Fin m → ℂ) →ₗ[ℂ] (X → Fin m → ℂ) :=
  LinearMap.pi fun x =>
    (Matrix.mulVecLin (leibnizJetMatrix m (Wj x))).comp (LinearMap.proj x)

omit [Fintype X] in
theorem leibnizBlockLin_apply (m : ℕ) (Wj : X → ℕ → ℂ) (v : X → Fin m → ℂ) (x : X) :
    leibnizBlockLin m Wj v x = (leibnizJetMatrix m (Wj x)).mulVec (v x) := by
  rw [leibnizBlockLin, LinearMap.pi_apply, LinearMap.comp_apply]
  rfl

omit [Fintype X] in
theorem surjective_leibnizBlockLin (m : ℕ) (Wj : X → ℕ → ℂ) (hW : ∀ x, Wj x 0 ≠ 0) :
    Function.Surjective (leibnizBlockLin m Wj) := by
  classical
  intro target
  have hsurj : ∀ x, Function.Surjective (leibnizJetMatrix m (Wj x)).mulVec := fun x =>
    surjective_mulVec_of_det_ne_zero (det_leibnizJetMatrix_ne_zero m (hW x))
  choose w hw using fun x => hsurj x (target x)
  refine ⟨w, ?_⟩
  funext x
  rw [leibnizBlockLin_apply]
  exact hw x

/-! ### The probe jet packet -/

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The finite jet packet of a gauged source with a polynomial probe added to the exponent. -/
def gaugeProbeJetPacket (W g : ℂ → ℂ) {m D : ℕ} (pd : GaugeProbe X m D) (nodes : H → X → ℂ)
    (p : (Fin D → ℂ) × H) : X → Fin m → ℂ :=
  leibnizBlockLin m (fun x r => iteratedDeriv r W (nodes p.2 x))
    (blockJetMap m (fun _ : X => expJetMap m)
      (fun x => gaugeJetVec m g (nodes p.2 x) + pd.jet (nodes p.2) p.1 x))

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- **The probe jet packet is the actual jet packet of the perturbed gauged source.** -/
theorem gaugeProbeJetPacket_eq {W g : ℂ → ℂ} (hW : Differentiable ℂ W) (hg : Differentiable ℂ g)
    {m D : ℕ} (pd : GaugeProbe X m D) (nodes : H → X → ℂ) (p : (Fin D → ℂ) × H) (x : X)
    (j : Fin m) :
    gaugeProbeJetPacket W g pd nodes p x j
      = iteratedDeriv (j : ℕ)
          (fun w => W w * Complex.exp (g w + Polynomial.eval w (pd.poly p.1)))
          (nodes p.2 x) := by
  have hpoly : Differentiable ℂ (fun w => Polynomial.eval w (pd.poly p.1)) :=
    Polynomial.differentiable _
  have hsum : Differentiable ℂ (fun w => g w + Polynomial.eval w (pd.poly p.1)) :=
    fun w => (hg w).add (hpoly w)
  rw [iteratedDeriv_gaugeCarrier hW hsum (nodes p.2 x) j]
  rw [gaugeProbeJetPacket, leibnizBlockLin_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  rw [blockJetMap, gaugeJetVec_add hg hpoly, pd.jet_eq (nodes p.2) p.1 x]

/-! ### The derivative in the probe direction -/

/-- The derivative of the probe jet packet: probe jets, exponential jets, Leibniz. -/
def gaugeProbeJetCLM (W g : ℂ → ℂ) {m D : ℕ} (pd : GaugeProbe X m D) (nodes : H → X → ℂ)
    (c : Fin D → ℂ) (h : H) : (Fin D → ℂ) →L[ℝ] (X → Fin m → ℂ) :=
  ((LinearMap.toContinuousLinearMap
      (leibnizBlockLin m (fun x r => iteratedDeriv r W (nodes h x)))).restrictScalars ℝ).comp
    ((blockJetCLM m (fun x =>
        (expJetJacobianCLM m (gaugeJetVec m g (nodes h x)
          + pd.jet (nodes h) c x)).restrictScalars ℝ)).comp (pd.jet (nodes h)))

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem hasFDerivAt_gaugeProbeJetPacket (W g : ℂ → ℂ) {m D : ℕ} (pd : GaugeProbe X m D)
    (nodes : H → X → ℂ) (c : Fin D → ℂ) (h : H) :
    HasFDerivAt (fun v => gaugeProbeJetPacket W g pd nodes (v, h))
      (gaugeProbeJetCLM W g pd nodes c h) c := by
  set Lprobe := pd.jet (nodes h) with hLprobe
  set G : X → Fin m → ℂ := fun x => gaugeJetVec m g (nodes h x) with hG
  have haff : HasFDerivAt (fun v : Fin D → ℂ => G + Lprobe v) Lprobe c :=
    (Lprobe.hasFDerivAt).const_add G
  have hblock : HasFDerivAt (blockJetMap m (fun _ : X => expJetMap m))
      (blockJetCLM m (fun x => (expJetJacobianCLM m ((G + Lprobe c) x)).restrictScalars ℝ))
      (G + Lprobe c) :=
    hasFDerivAt_blockJetMap m (fun _ : X => expJetMap m) _ _
      (fun x => (hasFDerivAt_expJetMap m ((G + Lprobe c) x)).restrictScalars ℝ)
  have hcomp := hblock.comp c haff
  have hlin := ((LinearMap.toContinuousLinearMap
      (leibnizBlockLin m (fun x r => iteratedDeriv r W (nodes h x)))).restrictScalars
      ℝ).hasFDerivAt (x := blockJetMap m (fun _ : X => expJetMap m) (G + Lprobe c))
  have hfinal := hlin.comp c hcomp
  refine hfinal.congr_of_eventuallyEq ?_
  filter_upwards [] with v
  rfl

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
theorem surjective_gaugeProbeJetCLM {W g : ℂ → ℂ} {m D : ℕ} (pd : GaugeProbe X m D)
    (nodes : H → X → ℂ) (c : Fin D → ℂ) (h : H)
    (hprobe : Function.Surjective (pd.jet (nodes h)))
    (hW : ∀ x, W (nodes h x) ≠ 0) :
    Function.Surjective (gaugeProbeJetCLM W g pd nodes c h) := by
  intro y
  have hTheta : Function.Surjective
      (leibnizBlockLin m (fun x r => iteratedDeriv r W (nodes h x))) := by
    refine surjective_leibnizBlockLin m _ fun x => ?_
    rw [iteratedDeriv_zero]
    exact hW x
  obtain ⟨y1, hy1⟩ := hTheta y
  have hExp : Function.Surjective (blockJetCLM m (fun x =>
      (expJetJacobianCLM m (gaugeJetVec m g (nodes h x)
        + pd.jet (nodes h) c x)).restrictScalars ℝ)) := by
    refine surjective_blockJetCLM m _ fun x t => ?_
    obtain ⟨w, hw⟩ := surjective_mulVec_of_det_ne_zero
      (det_expJetJacobian_ne_zero m (gaugeJetVec m g (nodes h x)
        + pd.jet (nodes h) c x)) t
    refine ⟨w, ?_⟩
    show expJetJacobianCLM m _ w = t
    rw [expJetJacobianCLM_apply, hw]
  obtain ⟨y2, hy2⟩ := hExp y1
  obtain ⟨y3, hy3⟩ := hprobe y2
  refine ⟨y3, ?_⟩
  show leibnizBlockLin m (fun x r => iteratedDeriv r W (nodes h x))
      (blockJetCLM m (fun x =>
        (expJetJacobianCLM m (gaugeJetVec m g (nodes h x)
          + pd.jet (nodes h) c x)).restrictScalars ℝ)
        (pd.jet (nodes h) y3)) = y
  rw [hy3, hy2, hy1]

/-! ### Joint smoothness of the probe jet packet -/

theorem contDiff_nodeComp {D : ℕ} {F : ℂ → ℂ} (hF : Differentiable ℂ F) {nodes : H → X → ℂ}
    (hnodes : ContDiff ℝ ⊤ nodes) (x : X) :
    ContDiff ℝ ⊤ (fun p : (Fin D → ℂ) × H => F (nodes p.2 x)) :=
  (contDiff_of_entire hF).comp
    (((contDiff_apply ℝ ℂ x).comp hnodes).comp contDiff_snd)

theorem contDiff_gaugeJetVec_node {D : ℕ} {g : ℂ → ℂ} (hg : Differentiable ℂ g) (m : ℕ)
    {nodes : H → X → ℂ} (hnodes : ContDiff ℝ ⊤ nodes) (x : X) :
    ContDiff ℝ ⊤ (fun p : (Fin D → ℂ) × H => gaugeJetVec m g (nodes p.2 x)) := by
  rw [contDiff_pi]
  intro k
  exact contDiff_nodeComp (differentiable_iteratedDeriv_of_entire hg (k : ℕ)) hnodes x

theorem contDiff_probeJet_node {m D : ℕ} (pd : GaugeProbe X m D) {nodes : H → X → ℂ}
    (hnodes : ContDiff ℝ ⊤ nodes) (x : X) :
    ContDiff ℝ ⊤ (fun p : (Fin D → ℂ) × H => pd.jet (nodes p.2) p.1 x) := by
  rw [contDiff_pi]
  intro k
  have hfun : (fun p : (Fin D → ℂ) × H => pd.jet (nodes p.2) p.1 x k)
      = fun p : (Fin D → ℂ) × H =>
        (Polynomial.derivative^[(k : ℕ)] (pd.poly p.1)).eval (nodes p.2 x) := by
    funext p
    rw [congrFun (pd.jet_eq (nodes p.2) p.1 x) k, gaugeJetVec, iteratedDeriv_polynomial_eval]
  rw [hfun]
  exact (pd.polyJet_contDiff (k : ℕ)).comp
    (contDiff_fst.prodMk (((contDiff_apply ℝ ℂ x).comp hnodes).comp contDiff_snd))

/-- **The probe jet packet is jointly smooth in the probe and the shift.** -/
theorem contDiff_gaugeProbeJetPacket {W g : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hg : Differentiable ℂ g) {m D : ℕ} (pd : GaugeProbe X m D) {nodes : H → X → ℂ}
    (hnodes : ContDiff ℝ ⊤ nodes) :
    ContDiff ℝ ⊤ (gaugeProbeJetPacket W g pd nodes) := by
  classical
  rw [contDiff_pi]
  intro x
  rw [contDiff_pi]
  intro j
  have hv : ContDiff ℝ ⊤ (fun p : (Fin D → ℂ) × H =>
      gaugeJetVec m g (nodes p.2 x) + pd.jet (nodes p.2) p.1 x) :=
    (contDiff_gaugeJetVec_node hg m hnodes x).add (contDiff_probeJet_node pd hnodes x)
  have hexp : ContDiff ℝ ⊤ (fun p : (Fin D → ℂ) × H =>
      expJetMap m (gaugeJetVec m g (nodes p.2 x) + pd.jet (nodes p.2) p.1 x)) :=
    (contDiff_real_expJetMap m).comp hv
  have hfun : (fun p : (Fin D → ℂ) × H => gaugeProbeJetPacket W g pd nodes p x j)
      = fun p : (Fin D → ℂ) × H => ∑ l : Fin m,
          leibnizJetMatrix m (fun r => iteratedDeriv r W (nodes p.2 x)) j l *
            expJetMap m (gaugeJetVec m g (nodes p.2 x) + pd.jet (nodes p.2) p.1 x) l := by
    funext p
    rw [gaugeProbeJetPacket, leibnizBlockLin_apply, Matrix.mulVec, dotProduct]
    rfl
  rw [hfun]
  refine ContDiff.sum fun l _ => ?_
  refine ContDiff.mul ?_ (((contDiff_apply ℝ ℂ l).comp hexp))
  have hcoeff : (fun p : (Fin D → ℂ) × H =>
        leibnizJetMatrix m (fun r => iteratedDeriv r W (nodes p.2 x)) j l)
      = fun p : (Fin D → ℂ) × H =>
        if (l : ℕ) ≤ (j : ℕ) then ((Nat.choose (j : ℕ) (l : ℕ) : ℂ)) *
          iteratedDeriv ((j : ℕ) - (l : ℕ)) W (nodes p.2 x) else 0 := by
    funext p
    rfl
  rw [hcoeff]
  by_cases hjl : (l : ℕ) ≤ (j : ℕ)
  · simp only [if_pos hjl]
    exact contDiff_const.mul
      (contDiff_nodeComp (differentiable_iteratedDeriv_of_entire hW _) hnodes x)
  · simp only [if_neg hjl]
    exact contDiff_const

end

end GaloisForLFunctions.HTGeometry
