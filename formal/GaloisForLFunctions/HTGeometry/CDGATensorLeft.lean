import GaloisForLFunctions.HTGeometry.CDGATensor

/-!
# Distributivity and twists in the left variable of a tensor product

The mirror of the right-variable theory.  A degree-one family applied in the *left* factor carries
no Koszul sign, because the left half-differential carries none; the sign that made the right-hand
theory work reappears here as the sign in the compatibility of the family with the algebra action,
and as the sign of the right half-differential, which now anticommutes with the family for free.

* `HTGeometry.tensorSigmaL` : a degree-one family applied in the left factor.
* `HTGeometry.tensorTwistL` : the twist induced on a tensor product by a twist of the left factor.
* `HTGeometry.tensorProdLeft` : distributivity over a product in the left variable.
* `HTGeometry.tensorProdLeftHom` : tensoring commutes with attaching a cell to the left factor.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {D : ℕ → Type w} [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

section SigmaL

/-- A degree-one family of maps `D → M`, applied in the left factor of a tensor product.  With the
family a differential this is `tensorDL`; with it a twisting cochain it is the twist induced on the
tensor product.  No Koszul sign appears: the left factor is the first one. -/
def tensorSigmaL (σ : ∀ n, D n →ₗ[R] M (n + 1)) (m : ℕ)
    (f : TensorCarrier (R := R) D N m) : TensorCarrier (R := R) M N (m + 1) :=
  fun p =>
    match p with
    | ⟨(0, _), _⟩ => 0
    | ⟨(a + 1, b), h⟩ =>
        TensorProduct.map (σ a) LinearMap.id (f ⟨(a, b), by omega⟩)

@[simp] theorem tensorSigmaL_zero (σ : ∀ n, D n →ₗ[R] M (n + 1)) (m b : ℕ)
    (f : TensorCarrier (R := R) D N m) (h : (0, b).1 + (0, b).2 = m + 1) :
    tensorSigmaL (N := N) σ m f ⟨(0, b), h⟩ = 0 := rfl

@[simp] theorem tensorSigmaL_succ (σ : ∀ n, D n →ₗ[R] M (n + 1)) (m a b : ℕ)
    (f : TensorCarrier (R := R) D N m) (h : (a + 1, b).1 + (a + 1, b).2 = m + 1) :
    tensorSigmaL (N := N) σ m f ⟨(a + 1, b), h⟩
      = TensorProduct.map (σ a) LinearMap.id (f ⟨(a, b), by omega⟩) := rfl

theorem tensorSigmaL_add (σ : ∀ n, D n →ₗ[R] M (n + 1)) (m : ℕ)
    (f g : TensorCarrier (R := R) D N m) :
    tensorSigmaL (N := N) σ m (f + g)
      = tensorSigmaL (N := N) σ m f + tensorSigmaL (N := N) σ m g := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero => rfl
  | succ a' =>
      show TensorProduct.map (σ a') LinearMap.id ((f + g) ⟨(a', b), by omega⟩) = _
      rw [tensorCarrier_add_apply, map_add]
      rfl

theorem tensorSigmaL_smul (σ : ∀ n, D n →ₗ[R] M (n + 1)) (m : ℕ) (r : R)
    (f : TensorCarrier (R := R) D N m) :
    tensorSigmaL (N := N) σ m (r • f) = r • tensorSigmaL (N := N) σ m f := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a with
  | zero => rfl
  | succ a' =>
      show TensorProduct.map (σ a') LinearMap.id ((r • f) ⟨(a', b), by omega⟩) = _
      rw [tensorCarrier_smul_apply, map_smul]
      rfl

/-- `tensorDL` is the case of `tensorSigmaL` where the family is the differential. -/
theorem tensorDL_eq_tensorSigmaL (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (n : ℕ) (f : TensorCarrier (R := R) M N n) :
    tensorDL P Q n f = tensorSigmaL (N := N) (fun k => P.dₗ k) n f := rfl

/-- A left-factor family composed with the two differentials, in the left factor. -/
theorem tensorMap_sigmaL_d_apply (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    (σ : ∀ n, D n →ₗ[R] M (n + 1))
    (hσ : ∀ (k : ℕ) (z : D k), P.d (k + 1) (σ k z) + σ (k + 1) (Pc.d k z) = 0)
    (a b : ℕ) (z : TensorProduct R (D a) (N b)) :
    TensorProduct.map (P.dₗ (a + 1)) (LinearMap.id : N b →ₗ[R] N b)
        (TensorProduct.map (σ a) (LinearMap.id : N b →ₗ[R] N b) z)
      + TensorProduct.map (σ (a + 1)) (LinearMap.id : N b →ₗ[R] N b)
        (TensorProduct.map (Pc.dₗ a) (LinearMap.id : N b →ₗ[R] N b) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, ← TensorProduct.add_tmul]
      show (P.d (a + 1) (σ a x) + σ (a + 1) (Pc.d a x)) ⊗ₜ[R]
        (LinearMap.id (LinearMap.id y) : N b) = 0
      rw [hσ a x, TensorProduct.zero_tmul]
  | add z w hz hw =>
      simp only [map_add]
      rw [add_add_add_comm, hz, hw, add_zero]

/-- **The left half-differential and a left-factor family anticommute** as soon as the family
anticommutes with the differentials of the two modules it connects. -/
theorem tensorDL_tensorSigmaL_add (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    (Q : CDGAModuleStructure A N) (σ : ∀ n, D n →ₗ[R] M (n + 1))
    (hσ : ∀ (k : ℕ) (z : D k), P.d (k + 1) (σ k z) + σ (k + 1) (Pc.d k z) = 0) (n : ℕ)
    (f : TensorCarrier (R := R) D N n) :
    tensorDL P Q (n + 1) (tensorSigmaL (N := N) σ n f)
      + tensorSigmaL (N := N) σ (n + 1) (tensorDL Pc Q n f) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  show tensorDL P Q (n + 1) (tensorSigmaL (N := N) σ n f) ⟨(a, b), h⟩
      + tensorSigmaL (N := N) σ (n + 1) (tensorDL Pc Q n f) ⟨(a, b), h⟩ = 0
  cases a with
  | zero => simp only [tensorDL_zero, tensorSigmaL_zero, add_zero]
  | succ a' =>
      cases a' with
      | zero =>
          rw [tensorDL_succ, tensorSigmaL_zero, map_zero, tensorSigmaL_succ, tensorDL_zero,
            map_zero, add_zero]
      | succ a'' =>
          rw [tensorDL_succ, tensorSigmaL_succ, tensorSigmaL_succ, tensorDL_succ,
            tensorMap_sigmaL_d_apply P Pc σ hσ a'' b (f ⟨(a'', b), by omega⟩)]

/-- **The right half-differential and a left-factor family anticommute.**  No property of the family
is used: the sign comes from the shift of the left degree by one. -/
theorem tensorDR_tensorSigmaL_add (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    (Q : CDGAModuleStructure A N) (σ : ∀ n, D n →ₗ[R] M (n + 1)) (n : ℕ)
    (f : TensorCarrier (R := R) D N n) :
    tensorDR P Q (n + 1) (tensorSigmaL (N := N) σ n f)
      + tensorSigmaL (N := N) σ (n + 1) (tensorDR Pc Q n f) = 0 := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  show tensorDR P Q (n + 1) (tensorSigmaL (N := N) σ n f) ⟨(a, b), h⟩
      + tensorSigmaL (N := N) σ (n + 1) (tensorDR Pc Q n f) ⟨(a, b), h⟩ = 0
  cases a with
  | zero =>
      cases b with
      | zero => simp only [tensorDR_zero, tensorSigmaL_zero, add_zero]
      | succ b' =>
          rw [tensorDR_succ, tensorSigmaL_zero, map_zero, smul_zero, tensorSigmaL_zero, add_zero]
  | succ a' =>
      cases b with
      | zero =>
          rw [tensorDR_zero, tensorSigmaL_succ, tensorDR_zero, map_zero, zero_add]
      | succ b' =>
          rw [tensorDR_succ, tensorSigmaL_succ, tensorSigmaL_succ, tensorDR_succ, map_smul]
          have hcomm := congrArg
            (fun L : TensorProduct R (D a') (N b') →ₗ[R] TensorProduct R (M (a' + 1)) (N (b' + 1))
              => L (f ⟨(a', b'), by omega⟩))
            (show (TensorProduct.map (LinearMap.id : M (a' + 1) →ₗ[R] M (a' + 1)) (Q.dₗ b')).comp
                (TensorProduct.map (σ a') (LinearMap.id : N b' →ₗ[R] N b'))
              = (TensorProduct.map (σ a') (LinearMap.id : N (b' + 1) →ₗ[R] N (b' + 1))).comp
                (TensorProduct.map (LinearMap.id : D a' →ₗ[R] D a') (Q.dₗ b')) by
              rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id,
                LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp])
          simp only [LinearMap.comp_apply] at hcomm
          rw [hcomm, pow_succ, mul_comm, neg_one_mul, neg_smul, neg_add_cancel]

/-- **The total differential and a left-factor family anticommute.** -/
theorem tensorD_tensorSigmaL_add (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    (Q : CDGAModuleStructure A N) (σ : ∀ n, D n →ₗ[R] M (n + 1))
    (hσ : ∀ (k : ℕ) (z : D k), P.d (k + 1) (σ k z) + σ (k + 1) (Pc.d k z) = 0) (n : ℕ)
    (f : TensorCarrier (R := R) D N n) :
    tensorD P Q (n + 1) (tensorSigmaL (N := N) σ n f)
      + tensorSigmaL (N := N) σ (n + 1) (tensorD Pc Q n f) = 0 := by
  have hL := tensorDL_tensorSigmaL_add P Pc Q σ hσ n f
  have hR := tensorDR_tensorSigmaL_add P Pc Q σ n f
  show tensorDL P Q (n + 1) (tensorSigmaL (N := N) σ n f)
      + tensorDR P Q (n + 1) (tensorSigmaL (N := N) σ n f)
      + tensorSigmaL (N := N) σ (n + 1) (tensorDL Pc Q n f + tensorDR Pc Q n f) = 0
  rw [tensorSigmaL_add, add_add_add_comm, hL, hR, add_zero]

/-- **The Leibniz rule for a left-factor family under the action.**  The sign is the one the family
already carries against the algebra. -/
theorem tensorSigmaL_tensorAct (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    (Q : CDGAModuleStructure A N) (σ : ∀ n, D n →ₗ[R] M (n + 1))
    (hσ : ∀ {c i k : ℕ} (e : c + i = k) (x : X c) (z : D i),
      σ k (Pc.act e x z)
        = ((-1 : R)) ^ c • P.act (show c + (i + 1) = k + 1 by omega) x (σ i z))
    {b n m : ℕ} (h : b + n = m) (x : X b) (f : TensorCarrier (R := R) D N n) :
    tensorSigmaL (N := N) σ m (tensorAct Pc Q h x f)
      = ((-1 : R)) ^ b • tensorAct P Q (show b + (n + 1) = m + 1 by omega) x
          (tensorSigmaL (N := N) σ n f) := by
  funext p
  obtain ⟨⟨a, c⟩, ha⟩ := p
  cases a with
  | zero =>
      rw [tensorSigmaL_zero, tensorCarrier_smul_apply]
      by_cases hb : b ≤ 0
      · rw [tensorAct_apply_eq P Q (show b + (n + 1) = m + 1 by omega) x
            (tensorSigmaL (N := N) σ n f) (show b + 0 = 0 by omega)
            (show (0, c).1 + (0, c).2 = n + 1 by omega) ha,
          tensorSigmaL_zero, map_zero, smul_zero]
      · rw [tensorAct_of_lt P Q (show b + (n + 1) = m + 1 by omega) x
            (tensorSigmaL (N := N) σ n f) ha hb, smul_zero]
  | succ a' =>
      by_cases hb : b ≤ a'
      · obtain ⟨i, hi⟩ : ∃ i, b + i = a' := Nat.le.dest hb
        rw [tensorSigmaL_succ,
          tensorAct_apply_eq Pc Q h x f hi (show (i, c).1 + (i, c).2 = n by omega)
            (show (a', c).1 + (a', c).2 = m by omega),
          tensorCarrier_smul_apply,
          tensorAct_apply_eq P Q (show b + (n + 1) = m + 1 by omega) x
            (tensorSigmaL (N := N) σ n f) (show b + (i + 1) = a' + 1 by omega)
            (show (i + 1, c).1 + (i + 1, c).2 = n + 1 by omega) ha,
          tensorSigmaL_succ]
        have hmap : (TensorProduct.map (σ a') (LinearMap.id : N c →ₗ[R] N c)).comp
              (TensorProduct.map (Pc.actₗ hi x) (LinearMap.id : N c →ₗ[R] N c))
            = ((-1 : R)) ^ b • (TensorProduct.map
                (P.actₗ (show b + (i + 1) = a' + 1 by omega) x)
                (LinearMap.id : N c →ₗ[R] N c)).comp
              (TensorProduct.map (σ i) (LinearMap.id : N c →ₗ[R] N c)) := by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
          simp only [LinearMap.comp_id]
          have hl : (σ a').comp (Pc.actₗ hi x)
              = ((-1 : R)) ^ b • (P.actₗ (show b + (i + 1) = a' + 1 by omega) x).comp (σ i) :=
            LinearMap.ext fun z => hσ hi x z
          rw [hl, TensorProduct.map_smul_left]
        have hval := congrArg (fun L : TensorProduct R (D i) (N c) →ₗ[R]
          TensorProduct R (M (a' + 1)) (N c) => L (f ⟨(i, c), by omega⟩)) hmap
        simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hval
        exact hval
      · by_cases hb2 : b ≤ a' + 1
        · rw [tensorSigmaL_succ,
            tensorAct_of_lt Pc Q h x f (show (a', c).1 + (a', c).2 = m by omega) hb, map_zero,
            tensorCarrier_smul_apply,
            tensorAct_apply_eq P Q (show b + (n + 1) = m + 1 by omega) x
              (tensorSigmaL (N := N) σ n f) (show b + 0 = a' + 1 by omega)
              (show (0, c).1 + (0, c).2 = n + 1 by omega) ha,
            tensorSigmaL_zero, map_zero, smul_zero]
        · rw [tensorSigmaL_succ,
            tensorAct_of_lt Pc Q h x f (show (a', c).1 + (a', c).2 = m by omega) hb, map_zero,
            tensorCarrier_smul_apply,
            tensorAct_of_lt P Q (show b + (n + 1) = m + 1 by omega) x
              (tensorSigmaL (N := N) σ n f) ha hb2, smul_zero]

/-- **The twist induced on a tensor product by a twist of the left factor.** -/
def tensorTwistL {P : CDGAModuleStructure A M} {Pc : CDGAModuleStructure A D}
    (t : CDGATwist P Pc) (Q : CDGAModuleStructure A N) :
    CDGATwist (tensorModule P Q) (tensorModule Pc Q) where
  τ n v := tensorSigmaL (N := N) (fun k => t.τₗ k) n v
  τ_add n v v' := tensorSigmaL_add (N := N) (fun k => t.τₗ k) n v v'
  τ_smul n r v := tensorSigmaL_smul (N := N) (fun k => t.τₗ k) n r v
  τ_act h x v := by
    rw [tensorModule_act, tensorModule_act]
    exact tensorSigmaL_tensorAct P Pc Q (fun k => t.τₗ k)
      (fun e y z => t.τ_act e y z) h x v
  τ_d n v := by
    rw [tensorModule_d, tensorModule_d]
    exact tensorD_tensorSigmaL_add P Pc Q (fun k => t.τₗ k) (fun k z => t.τ_d k z) n v

@[simp] theorem tensorTwistL_τ {P : CDGAModuleStructure A M} {Pc : CDGAModuleStructure A D}
    (t : CDGATwist P Pc) (Q : CDGAModuleStructure A N) (n : ℕ)
    (v : TensorCarrier (R := R) D N n) :
    (tensorTwistL t Q).τ n v = tensorSigmaL (N := N) (fun k => t.τₗ k) n v := rfl

end SigmaL

section Distributivity

/-- **The tensor product distributes over a direct sum in the first variable**, bidegree by
bidegree. -/
noncomputable def tensorProdLeft (n : ℕ) :
    TensorCarrier (R := R) (fun k => M k × D k) N n
      ≃ₗ[R] TensorCarrier (R := R) M N n × TensorCarrier (R := R) D N n where
  toFun f :=
    (fun p => (TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2) (f p)).1,
     fun p => (TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2) (f p)).2)
  map_add' f g := by
    refine Prod.ext ?_ ?_
    · funext p
      show ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)) (f p + g p)).1 = _
      rw [map_add]
      rfl
    · funext p
      show ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)) (f p + g p)).2 = _
      rw [map_add]
      rfl
  map_smul' r f := by
    refine Prod.ext ?_ ?_
    · funext p
      show ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)) (r • f p)).1 = _
      rw [map_smul]
      rfl
    · funext p
      show ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)) (r • f p)).2 = _
      rw [map_smul]
      rfl
  invFun g := fun p =>
    (TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)).symm (g.1 p, g.2 p)
  left_inv f := by
    funext p
    show (TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)).symm
      ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)) (f p)) = f p
    rw [LinearEquiv.symm_apply_apply]
  right_inv g := by
    refine Prod.ext ?_ ?_
    · funext p
      show ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2))
        ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)).symm (g.1 p, g.2 p))).1 = _
      rw [LinearEquiv.apply_symm_apply]
    · funext p
      show ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2))
        ((TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2)).symm (g.1 p, g.2 p))).2 = _
      rw [LinearEquiv.apply_symm_apply]

theorem tensorProdLeft_bijective (n : ℕ) :
    Function.Bijective (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n) :=
  (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n).toEquiv.bijective

@[simp] theorem tensorProdLeft_fst (n : ℕ)
    (f : TensorCarrier (R := R) (fun k => M k × D k) N n)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1 p
      = (TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2) (f p)).1 := rfl

@[simp] theorem tensorProdLeft_snd (n : ℕ)
    (f : TensorCarrier (R := R) (fun k => M k × D k) N n)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) :
    (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2 p
      = (TensorProduct.prodLeft R R (M p.1.1) (D p.1.1) (N p.1.2) (f p)).2 := rfl

variable {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]

/-- Distributivity commutes with a map applied in the right factor: first component. -/
theorem prodLeft_map_right_fst {a b b' : ℕ} (ψ : N b →ₗ[R] N' b')
    (z : TensorProduct R (M a × D a) (N b)) :
    (TensorProduct.prodLeft R R (M a) (D a) (N' b')
        (TensorProduct.map (LinearMap.id : (M a × D a) →ₗ[R] (M a × D a)) ψ z)).1
      = TensorProduct.map (LinearMap.id : M a →ₗ[R] M a) ψ
          (TensorProduct.prodLeft R R (M a) (D a) (N b) z).1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w =>
      obtain ⟨x₁, x₂⟩ := x
      simp
  | add z w hz hw => simp only [map_add, Prod.fst_add, hz, hw]

/-- Distributivity commutes with a map applied in the right factor: second component. -/
theorem prodLeft_map_right_snd {a b b' : ℕ} (ψ : N b →ₗ[R] N' b')
    (z : TensorProduct R (M a × D a) (N b)) :
    (TensorProduct.prodLeft R R (M a) (D a) (N' b')
        (TensorProduct.map (LinearMap.id : (M a × D a) →ₗ[R] (M a × D a)) ψ z)).2
      = TensorProduct.map (LinearMap.id : D a →ₗ[R] D a) ψ
          (TensorProduct.prodLeft R R (M a) (D a) (N b) z).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w =>
      obtain ⟨x₁, x₂⟩ := x
      simp
  | add z w hz hw => simp only [map_add, Prod.snd_add, hz, hw]

/-- Distributivity turns a triangular map of the left factor into the two half-maps it is made of. -/
theorem prodLeft_map_left_fst {a a' b : ℕ} (φ₁ : M a →ₗ[R] M a') (φ₂ : D a →ₗ[R] M a')
    (g : (M a × D a) →ₗ[R] (M a' × D a')) (hg : ∀ w : M a × D a, (g w).1 = φ₁ w.1 + φ₂ w.2)
    (z : TensorProduct R (M a × D a) (N b)) :
    (TensorProduct.prodLeft R R (M a') (D a') (N b)
        (TensorProduct.map g (LinearMap.id : N b →ₗ[R] N b) z)).1
      = TensorProduct.map φ₁ (LinearMap.id : N b →ₗ[R] N b)
          (TensorProduct.prodLeft R R (M a) (D a) (N b) z).1
        + TensorProduct.map φ₂ (LinearMap.id : N b →ₗ[R] N b)
          (TensorProduct.prodLeft R R (M a) (D a) (N b) z).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w =>
      obtain ⟨x₁, x₂⟩ := x
      show ((TensorProduct.prodLeft R R (M a') (D a') (N b))
        (TensorProduct.map g LinearMap.id ((x₁, x₂) ⊗ₜ[R] w))).1 = _
      rw [TensorProduct.map_tmul]
      show ((TensorProduct.prodLeft R R (M a') (D a') (N b))
        (((g (x₁, x₂)).1, (g (x₁, x₂)).2) ⊗ₜ[R] (LinearMap.id w : N b))).1 = _
      rw [TensorProduct.prodLeft_tmul, hg (x₁, x₂)]
      show (φ₁ x₁ + φ₂ x₂) ⊗ₜ[R] w = _
      rw [TensorProduct.add_tmul]
      rfl
  | add z w hz hw =>
      simp only [map_add, Prod.fst_add, Prod.snd_add, hz, hw]
      abel

/-- The second component of a triangular map of the left factor, after distributivity. -/
theorem prodLeft_map_left_snd {a a' b : ℕ} (φ₃ : D a →ₗ[R] D a')
    (g : (M a × D a) →ₗ[R] (M a' × D a')) (hg : ∀ w : M a × D a, (g w).2 = φ₃ w.2)
    (z : TensorProduct R (M a × D a) (N b)) :
    (TensorProduct.prodLeft R R (M a') (D a') (N b)
        (TensorProduct.map g (LinearMap.id : N b →ₗ[R] N b) z)).2
      = TensorProduct.map φ₃ (LinearMap.id : N b →ₗ[R] N b)
          (TensorProduct.prodLeft R R (M a) (D a) (N b) z).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x w =>
      obtain ⟨x₁, x₂⟩ := x
      show ((TensorProduct.prodLeft R R (M a') (D a') (N b))
        (TensorProduct.map g LinearMap.id ((x₁, x₂) ⊗ₜ[R] w))).2 = _
      rw [TensorProduct.map_tmul]
      show ((TensorProduct.prodLeft R R (M a') (D a') (N b))
        (((g (x₁, x₂)).1, (g (x₁, x₂)).2) ⊗ₜ[R] (LinearMap.id w : N b))).2 = _
      rw [TensorProduct.prodLeft_tmul, hg (x₁, x₂)]
      rfl
  | add z w hz hw => simp only [map_add, Prod.snd_add, hz, hw]

end Distributivity

section Transport

variable (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
  (Q : CDGAModuleStructure A N)

/-- Distributivity transports the right half-differential to the pair of right half-differentials. -/
theorem tensorProdLeft_tensorDR (t : CDGATwist P Pc) (n : ℕ)
    (f : TensorCarrier (R := R) (fun k => M k × D k) N n) :
    tensorProdLeft (R := R) (M := M) (D := D) (N := N) (n + 1)
        (tensorDR (CDGAModuleStructure.twisted P Pc t) Q n f)
      = (tensorDR P Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1,
         tensorDR Pc Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2) := by
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N b)
        (tensorDR (CDGAModuleStructure.twisted P Pc t) Q n f ⟨(a, b), h⟩)).1
      = tensorDR P Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1 ⟨(a, b), h⟩
    cases b with
    | zero => rw [tensorDR_zero, map_zero, Prod.fst_zero, tensorDR_zero]
    | succ b' =>
        rw [tensorDR_succ, map_smul, Prod.smul_fst, prodLeft_map_right_fst, tensorDR_succ,
          tensorProdLeft_fst]
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N b)
        (tensorDR (CDGAModuleStructure.twisted P Pc t) Q n f ⟨(a, b), h⟩)).2
      = tensorDR Pc Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2 ⟨(a, b), h⟩
    cases b with
    | zero => rw [tensorDR_zero, map_zero, Prod.snd_zero, tensorDR_zero]
    | succ b' =>
        rw [tensorDR_succ, map_smul, Prod.smul_snd, prodLeft_map_right_snd, tensorDR_succ,
          tensorProdLeft_snd]

/-- **Distributivity transports the left half-differential of a twisted left factor to the left
half-differential together with the induced twist.** -/
theorem tensorProdLeft_tensorDL (t : CDGATwist P Pc) (n : ℕ)
    (f : TensorCarrier (R := R) (fun k => M k × D k) N n) :
    tensorProdLeft (R := R) (M := M) (D := D) (N := N) (n + 1)
        (tensorDL (CDGAModuleStructure.twisted P Pc t) Q n f)
      = (tensorDL P Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1
            + tensorSigmaL (N := N) (fun k => t.τₗ k) n
              (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2,
         tensorDL Pc Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2) := by
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N b)
        (tensorDL (CDGAModuleStructure.twisted P Pc t) Q n f ⟨(a, b), h⟩)).1
      = (tensorDL P Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1
          + tensorSigmaL (N := N) (fun k => t.τₗ k) n
            (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2) ⟨(a, b), h⟩
    cases a with
    | zero =>
        rw [tensorDL_zero, map_zero, Prod.fst_zero, tensorCarrier_add_apply, tensorDL_zero,
          tensorSigmaL_zero, add_zero]
    | succ a' =>
        rw [tensorDL_succ,
          prodLeft_map_left_fst (P.dₗ a') (t.τₗ a')
            ((CDGAModuleStructure.twisted P Pc t).dₗ a') (fun w => rfl),
          tensorCarrier_add_apply, tensorDL_succ, tensorSigmaL_succ, tensorProdLeft_fst,
          tensorProdLeft_snd]
  · funext p
    obtain ⟨⟨a, b⟩, h⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N b)
        (tensorDL (CDGAModuleStructure.twisted P Pc t) Q n f ⟨(a, b), h⟩)).2
      = tensorDL Pc Q n (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2 ⟨(a, b), h⟩
    cases a with
    | zero => rw [tensorDL_zero, map_zero, Prod.snd_zero, tensorDL_zero]
    | succ a' =>
        rw [tensorDL_succ,
          prodLeft_map_left_snd (Pc.dₗ a') ((CDGAModuleStructure.twisted P Pc t).dₗ a')
            (fun w => rfl),
          tensorDL_succ, tensorProdLeft_snd]

/-- Distributivity transports the action to the componentwise action. -/
theorem tensorProdLeft_tensorAct (t : CDGATwist P Pc) {b n m : ℕ} (h : b + n = m) (x : X b)
    (f : TensorCarrier (R := R) (fun k => M k × D k) N n) :
    tensorProdLeft (R := R) (M := M) (D := D) (N := N) m
        (tensorAct (CDGAModuleStructure.twisted P Pc t) Q h x f)
      = (tensorAct P Q h x (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1,
         tensorAct Pc Q h x (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2) := by
  refine Prod.ext ?_ ?_
  · funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N c)
        (tensorAct (CDGAModuleStructure.twisted P Pc t) Q h x f ⟨(a, c), ha⟩)).1
      = tensorAct P Q h x
        (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1 ⟨(a, c), ha⟩
    by_cases hb : b ≤ a
    · obtain ⟨i, hi⟩ : ∃ i, b + i = a := Nat.le.dest hb
      rw [tensorAct_apply_eq (CDGAModuleStructure.twisted P Pc t) Q h x f hi (by omega) ha,
        prodLeft_map_left_fst (P.actₗ hi x) 0
          ((CDGAModuleStructure.twisted P Pc t).actₗ hi x) (fun w => (add_zero _).symm),
        tensorAct_apply_eq P Q h x
          (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1 hi (by omega) ha,
        tensorProdLeft_fst, TensorProduct.map_zero_left, LinearMap.zero_apply, add_zero]
    · rw [tensorAct_of_lt (CDGAModuleStructure.twisted P Pc t) Q h x f ha hb, map_zero,
        Prod.fst_zero,
        tensorAct_of_lt P Q h x
          (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).1 ha hb]
  · funext p
    obtain ⟨⟨a, c⟩, ha⟩ := p
    show (TensorProduct.prodLeft R R (M a) (D a) (N c)
        (tensorAct (CDGAModuleStructure.twisted P Pc t) Q h x f ⟨(a, c), ha⟩)).2
      = tensorAct Pc Q h x
        (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2 ⟨(a, c), ha⟩
    by_cases hb : b ≤ a
    · obtain ⟨i, hi⟩ : ∃ i, b + i = a := Nat.le.dest hb
      rw [tensorAct_apply_eq (CDGAModuleStructure.twisted P Pc t) Q h x f hi (by omega) ha,
        prodLeft_map_left_snd (Pc.actₗ hi x)
          ((CDGAModuleStructure.twisted P Pc t).actₗ hi x) (fun w => rfl),
        tensorAct_apply_eq Pc Q h x
          (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2 hi (by omega) ha,
        tensorProdLeft_snd]
    · rw [tensorAct_of_lt (CDGAModuleStructure.twisted P Pc t) Q h x f ha hb, map_zero,
        Prod.snd_zero,
        tensorAct_of_lt Pc Q h x
          (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f).2 ha hb]

/-- **Tensoring commutes with attaching a cell to the left factor.** -/
noncomputable def tensorProdLeftHom (t : CDGATwist P Pc) :
    CDGAModuleHom (tensorModule (CDGAModuleStructure.twisted P Pc t) Q)
      (CDGAModuleStructure.twisted (tensorModule P Q) (tensorModule Pc Q)
        (tensorTwistL t Q)) where
  toFun n f := tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f
  map_add n f g := map_add (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n) f g
  map_smul n c f := map_smul (tensorProdLeft (R := R) (M := M) (D := D) (N := N) n) c f
  map_act h x f := by
    show tensorProdLeft (R := R) (M := M) (D := D) (N := N) _
      (tensorAct (CDGAModuleStructure.twisted P Pc t) Q h x f) = _
    rw [tensorProdLeft_tensorAct]
    rfl
  map_d n f := by
    show tensorProdLeft (R := R) (M := M) (D := D) (N := N) (n + 1)
      (tensorD (CDGAModuleStructure.twisted P Pc t) Q n f) = _
    rw [show tensorD (CDGAModuleStructure.twisted P Pc t) Q n f
          = tensorDL (CDGAModuleStructure.twisted P Pc t) Q n f
            + tensorDR (CDGAModuleStructure.twisted P Pc t) Q n f from rfl,
      map_add, tensorProdLeft_tensorDL, tensorProdLeft_tensorDR]
    refine Prod.ext ?_ rfl
    show tensorDL P Q n _ + tensorSigmaL (N := N) (fun k => t.τₗ k) n _ + tensorDR P Q n _
      = tensorDL P Q n _ + tensorDR P Q n _ + tensorSigmaL (N := N) (fun k => t.τₗ k) n _
    rw [add_assoc, add_assoc, add_comm (tensorSigmaL (N := N) (fun k => t.τₗ k) n _)]

@[simp] theorem tensorProdLeftHom_toFun (t : CDGATwist P Pc) (n : ℕ)
    (f : TensorCarrier (R := R) (fun k => M k × D k) N n) :
    (tensorProdLeftHom P Pc Q t).toFun n f
      = tensorProdLeft (R := R) (M := M) (D := D) (N := N) n f := rfl

theorem tensorProdLeftHom_isQuasiIso (t : CDGATwist P Pc) :
    (tensorProdLeftHom P Pc Q t).IsQuasiIso :=
  CDGAModuleHom.IsQuasiIso.of_bijective (fun n => tensorProdLeft_bijective n)

end Transport

section RightNaturality

variable {N' : ℕ → Type w} [∀ n, AddCommGroup (N' n)] [∀ n, Module R (N' n)]

/-- **Tensoring in the right variable intertwines a left-factor family with itself.** -/
theorem tensorMapRight_tensorSigmaL (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    {Q : CDGAModuleStructure A N} {Q' : CDGAModuleStructure A N'} (ψ : CDGAModuleHom Q Q')
    (σ : ∀ n, D n →ₗ[R] M (n + 1)) (n : ℕ) (v : TensorCarrier (R := R) D N n) :
    (tensorMapRight P ψ).toFun (n + 1) (tensorSigmaL (N := N) σ n v)
      = tensorSigmaL (N := N') σ n ((tensorMapRight Pc ψ).toFun n v) := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  rw [tensorMapRight_toFun]
  cases a with
  | zero => rw [tensorSigmaL_zero, map_zero, tensorSigmaL_zero]
  | succ a' =>
      rw [tensorSigmaL_succ, tensorSigmaL_succ, tensorMapRight_toFun]
      have hcomm := congrArg
        (fun L : TensorProduct R (D a') (N b) →ₗ[R] TensorProduct R (M (a' + 1)) (N' b)
          => L (v ⟨(a', b), by omega⟩))
        (show (TensorProduct.map (LinearMap.id : M (a' + 1) →ₗ[R] M (a' + 1)) (ψ.mapₗ b)).comp
            (TensorProduct.map (σ a') (LinearMap.id : N b →ₗ[R] N b))
          = (TensorProduct.map (σ a') (LinearMap.id : N' b →ₗ[R] N' b)).comp
            (TensorProduct.map (LinearMap.id : D a' →ₗ[R] D a') (ψ.mapₗ b)) by
          rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id,
            LinearMap.id_comp, LinearMap.comp_id, LinearMap.id_comp])
      simp only [LinearMap.comp_apply] at hcomm
      rw [hcomm]

/-- The compatibility of the tensored comparison with the tensored twists, in the right variable. -/
theorem tensorTwistL_compat (P : CDGAModuleStructure A M) (Pc : CDGAModuleStructure A D)
    (Q : CDGAModuleStructure A N) (Q' : CDGAModuleStructure A N')
    {t : CDGATwist P Pc} (ψ : CDGAModuleHom Q Q') (n : ℕ)
    (v : TensorCarrier (R := R) D N n) :
    (tensorMapRight P ψ).toFun (n + 1) ((tensorTwistL t Q).τ n v)
      = (tensorTwistL t Q').τ n ((tensorMapRight Pc ψ).toFun n v) :=
  tensorMapRight_tensorSigmaL P Pc ψ (fun k => t.τₗ k) n v

end RightNaturality

end GaloisForLFunctions.HTGeometry
