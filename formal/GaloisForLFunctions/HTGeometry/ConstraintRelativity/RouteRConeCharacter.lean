import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.RelativeConeExactness

/-!
# The Route-R source complex and its relative cone character

The Route-R source datum is an algebra with a prime automorphism, an augmentation and a bilateral
Stokes regulator.  It presents a three-term cochain complex `A → A ⊕ ℂ → ℂ`, the regulator descends
to its degree-one cohomology, and the retained class `η = (0,1)` has regulator value one.  Any
comparison into a resolved complex therefore carries a relative cone character whose value on the
retained class is the physical coefficient.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## Complexes concentrated in three degrees -/

section Piece

variable {k : Type*} [Field k]

/-- Three modules placed in degrees `0`, `1`, `2`, with zero elsewhere. -/
@[reducible] def pieceCat (M₀ M₁ M₂ : ModuleCat.{0} k) : ℤ → ModuleCat.{0} k
  | 0 => M₀
  | 1 => M₁
  | 2 => M₂
  | _ => ModuleCat.of k PUnit

variable {M₀ M₁ M₂ : ModuleCat.{0} k}

/-- The three-term complex `M₀ → M₁ → M₂`, extended by zero. -/
noncomputable def truncComplex (d₀ : M₀ →ₗ[k] M₁) (d₁ : M₁ →ₗ[k] M₂)
    (h : ∀ x, d₁ (d₀ x) = 0) :
    ZCochain k (fun n => (pieceCat M₀ M₁ M₂ n : Type)) where
  d
    | 0 => d₀
    | 1 => d₁
    | 2 => 0
    | Int.ofNat (_ + 3) => 0
    | Int.negSucc _ => 0
  d_squared n x := by
    match n with
    | 0 => exact h x
    | 1 => rfl
    | 2 => rfl
    | Int.ofNat (_ + 3) => rfl
    | Int.negSucc 0 =>
      show d₀ ((0 : (pieceCat M₀ M₁ M₂ (Int.negSucc 0) : Type) →ₗ[k] (M₀ : Type)) x) = 0
      rw [LinearMap.zero_apply, map_zero]
    | Int.negSucc (_ + 1) => rfl

@[simp] theorem truncComplex_d_zero (d₀ : M₀ →ₗ[k] M₁) (d₁ : M₁ →ₗ[k] M₂)
    (h : ∀ x, d₁ (d₀ x) = 0) : (truncComplex d₀ d₁ h).d 0 = d₀ := rfl

@[simp] theorem truncComplex_d_one (d₀ : M₀ →ₗ[k] M₁) (d₁ : M₁ →ₗ[k] M₂)
    (h : ∀ x, d₁ (d₀ x) = 0) : (truncComplex d₀ d₁ h).d 1 = d₁ := rfl

end Piece
/-! ## The Route-R source datum -/

section RouteR

/-- A Route-R source datum: a prime transport `α`, an augmentation `ε` killed by the transport
defect, and a bilateral Stokes regulator `reg` that computes the augmentation on that defect. -/
structure RouteRSource (A : Type) [AddCommGroup A] [Module ℂ A] where
  /-- The prime transport. -/
  α : A →ₗ[ℂ] A
  /-- The augmentation. -/
  ε : A →ₗ[ℂ] ℂ
  /-- The bilateral Stokes regulator. -/
  reg : A →ₗ[ℂ] ℂ
  /-- The augmentation is transport invariant. -/
  eps_alpha : ∀ x, ε (α x) = ε x
  /-- The regulator computes the augmentation on the transport defect. -/
  reg_comm : ∀ x, reg (α x - x) = ε x

namespace RouteRSource

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)

/-- **Card `(RRC.6)`.**  The degree-zero differential `x ↦ (α x − x, ε x)`. -/
noncomputable def D₀ : A →ₗ[ℂ] (A × ℂ) := LinearMap.prod (S.α - LinearMap.id) S.ε

/-- **Card `(RRC.6)`.**  The degree-one differential `(y, z) ↦ ε y`. -/
noncomputable def D₁ : (A × ℂ) →ₗ[ℂ] ℂ := S.ε.comp (LinearMap.fst ℂ A ℂ)

theorem D₁_comp_D₀ (x : A) : S.D₁ (S.D₀ x) = 0 := by
  show S.ε (S.α x - x) = 0
  rw [map_sub, S.eps_alpha, sub_self]

/-- **Card `(RRC.5)`.**  The Route-R source complex `A → A ⊕ ℂ → ℂ`. -/
noncomputable def complex :
    ZCochain ℂ (fun n => (pieceCat (ModuleCat.of ℂ A) (ModuleCat.of ℂ (A × ℂ))
      (ModuleCat.of ℂ ℂ) n : Type)) :=
  truncComplex S.D₀ S.D₁ S.D₁_comp_D₀

set_option linter.unusedVariables false in
/-- **Card `(RRC.7)`.**  The retained source class `η = (0, 1)`. -/
noncomputable def eta (S : RouteRSource A) : (A × ℂ) := (0, 1)

theorem eta_mem_cocycles : (S.eta : A × ℂ) ∈ S.complex.cocycles 0 := by
  show S.D₁ S.eta = 0
  show S.ε (0 : A) = 0
  exact map_zero _

/-- **Card `(RRC.8)`.**  The bilateral Stokes regulator on degree-one cochains. -/
noncomputable def regulator : (A × ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.snd ℂ A ℂ - S.reg.comp (LinearMap.fst ℂ A ℂ)

/-- **Card `(RRC.8)`.**  The regulator kills coboundaries, hence descends. -/
theorem regulator_comp_D₀ (x : A) : S.regulator (S.D₀ x) = 0 := by
  show S.ε x - S.reg (S.α x - x) = 0
  rw [S.reg_comm, sub_self]

/-- **Card `(RRC.9)`.**  The regulator of the retained class is one. -/
theorem regulator_eta : S.regulator S.eta = 1 := by
  show (1 : ℂ) - S.reg (0 : A) = 1
  rw [map_zero, sub_zero]

/-- **Card `(RRC.9)`.**  The descended regulator on degree-one source cohomology. -/
noncomputable def regulatorBar : S.complex.cohomology 0 →ₗ[ℂ] ℂ :=
  sourceCharacter (C := S.complex) (V := ℂ) 0
    (show ((pieceCat (ModuleCat.of ℂ A) (ModuleCat.of ℂ (A × ℂ)) (ModuleCat.of ℂ ℂ) (0 + 1)) : Type) →ₗ[ℂ] ℂ from S.regulator)
    (fun b => S.regulator_comp_D₀ b)

theorem regulatorBar_eta :
    S.regulatorBar (S.complex.cls ⟨S.eta, S.eta_mem_cocycles⟩) = 1 := S.regulator_eta

/-- **Card `(RRC.13)`, `(RRC.27)`.**  The physical character attached to a coefficient and a
physical value. -/
noncomputable def physChar {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V) :
    (A × ℂ) →ₗ[ℂ] V :=
  (LinearMap.toSpanSingleton ℂ V v).comp ((cρ • LinearMap.id).comp S.regulator)

theorem physChar_comp_D₀ {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V) (x : A) :
    S.physChar cρ v (S.D₀ x) = 0 := by
  show (cρ • S.regulator (S.D₀ x)) • v = 0
  rw [S.regulator_comp_D₀, smul_zero, zero_smul]

theorem physChar_eta {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V) :
    S.physChar cρ v S.eta = cρ • v := by
  show (cρ • S.regulator S.eta) • v = cρ • v
  rw [S.regulator_eta, smul_eq_mul, mul_one]

end RouteRSource

/-! ## The relative cone character -/

section ConeCharacter

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)
  {Nfam : ℤ → Type} [∀ n, AddCommGroup (Nfam n)] [∀ n, Module ℂ (Nfam n)]
  {X : ZCochain ℂ Nfam} (Φ : ZCochainMap S.complex X)

/-- **Card `(RRC.11)`.**  A resolved primitive for the retained class produces a cone cocycle:
this is the class `κ = (L, η)`. -/
theorem cone_cocycle_of_primitive (L : Nfam 0)
    (hL : (Φ.f 1 S.eta : Nfam (0 + 1)) = X.d 0 L) :
    ((L, S.eta) : Nfam (-1 + 1) × (A × ℂ)) ∈ (coneComplex Φ).cocycles (-1) := by
  show (coneComplex Φ).d 0 (L, S.eta) = 0
  rw [coneComplex_d_apply]
  refine Prod.ext ?_ ?_
  · exact sub_eq_zero_of_eq hL.symm
  · show -(S.complex.d 1 S.eta) = 0
    have h : S.complex.d 1 S.eta = 0 := S.eta_mem_cocycles
    rw [h, neg_zero]

/-- **Card `(RRC.31)`, boxed.**  The relative cone character of the retained class is the physical
coefficient: the value depends only on the retained source class, never on the chosen resolved
primitive. -/
theorem coneCharacter_retained {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V)
    (y : (coneComplex Φ).cocycles (-1)) (hy : y.1.2 = S.eta) :
    coneCharacter Φ (-1) (S.physChar cρ v) (fun b => S.physChar_comp_D₀ cρ v b)
        ((coneComplex Φ).cls y)
      = cρ • v := by
  rw [coneCharacter_cls, hy]
  exact S.physChar_eta cρ v

/-- The character of the retained class computes the source character on the relative-law class it
names in the kernel of the comparison. -/
theorem coneCharacterRel_retained {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V)
    (z : (coneComplex Φ).cohomology (-1) ⧸
      LinearMap.range ((coneInc Φ).cohomologyMap (-1))) :
    coneCharacterRel Φ (-1) (S.physChar cρ v) (fun b => S.physChar_comp_D₀ cρ v b) z
      = sourceCharacter (C := S.complex) (-1 + 1) (S.physChar cρ v)
          (fun b => S.physChar_comp_D₀ cρ v b)
          ((coneRelativeLawEquiv Φ (-1) z : S.complex.cohomology (-1 + 1))) :=
  coneCharacterRel_eq Φ (-1) _ _ z

end ConeCharacter
/-! ## The fixed physical quotient `V = ℂ^𝒫 / ℓ¹(𝒫)` -/

section PhysicalQuotient

/-- **Card `(RRC.12)`.**  The summable ideal `ℓ¹(𝒫) ⊆ ℂ^𝒫`. -/
def ellOnePrimes : Submodule ℂ (Nat.Primes → ℂ) where
  carrier := {f | Summable fun p => ‖f p‖}
  add_mem' := fun {f g} hf hg =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => norm_add_le (f p) (g p))
      (hf.add hg)
  zero_mem' := by simp
  smul_mem' := fun c f hf => by simpa [norm_smul] using hf.mul_left ‖c‖

theorem mem_ellOnePrimes {f : Nat.Primes → ℂ} :
    f ∈ ellOnePrimes ↔ Summable fun p => ‖f p‖ := Iff.rfl

/-- **Card `(RRC.12)`.**  The fixed physical quotient `V = ℂ^𝒫/ℓ¹(𝒫)`. -/
abbrev physicalQuotient : Type := (Nat.Primes → ℂ) ⧸ ellOnePrimes

/-- **Card `(RRC.13)`.**  The Euler profile `F_t(p) = p^t · p/(p+1)²`. -/
noncomputable def eulerProfile (t : ℝ) : Nat.Primes → ℂ :=
  fun p => (((p : ℕ) : ℝ) ^ t * ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2 : ℝ)

theorem eulerProfile_nonneg (t : ℝ) (p : Nat.Primes) :
    (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ t * ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2 := by
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  positivity

theorem norm_eulerProfile (t : ℝ) (p : Nat.Primes) :
    ‖eulerProfile t p‖ = ((p : ℕ) : ℝ) ^ t * ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2 := by
  simp only [eulerProfile, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (eulerProfile_nonneg t p)

theorem two_le_prime_cast (p : Nat.Primes) : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
  exact_mod_cast p.2.two_le

/-- **Card `(RRC.14)`.**  Below the centre the Euler profile is summable, so its physical class
vanishes. -/
theorem eulerProfile_mem_of_neg {t : ℝ} (ht : t < 0) : eulerProfile t ∈ ellOnePrimes := by
  have hsum : Summable fun n : ℕ => 1 / ((n : ℝ) ^ (1 - t)) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun a b h => Subtype.ext h
  have hcomp : Summable fun p : Nat.Primes => 1 / (((p : ℕ) : ℝ) ^ (1 - t)) :=
    hsum.comp_injective hinj
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hcomp
  have h2 := two_le_prime_cast p
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hkey : ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / ((p : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hp0]
    nlinarith
  have hrw : (1 : ℝ) / (((p : ℕ) : ℝ) ^ (1 - t))
      = ((p : ℕ) : ℝ) ^ t / ((p : ℕ) : ℝ) := by
    rw [Real.rpow_sub hp0, Real.rpow_one, one_div_div]
  rw [norm_eulerProfile, hrw, mul_div_assoc]
  have hpow : (0 : ℝ) < ((p : ℕ) : ℝ) ^ t := Real.rpow_pos_of_pos hp0 t
  calc ((p : ℕ) : ℝ) ^ t * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2)
      ≤ ((p : ℕ) : ℝ) ^ t * (1 / ((p : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hkey hpow.le
    _ = ((p : ℕ) : ℝ) ^ t / ((p : ℕ) : ℝ) := by rw [mul_one_div]

/-- **Card `(RRC.14)`.**  At or above the centre the Euler profile is not summable, so its
physical class is nonzero.  The mechanism is the divergence of the prime harmonic series. -/
theorem eulerProfile_not_mem_of_nonneg {t : ℝ} (ht : 0 ≤ t) : eulerProfile t ∉ ellOnePrimes := by
  intro hmem
  refine Nat.Primes.not_summable_one_div ?_
  have h4 : Summable fun p : Nat.Primes => (4 : ℝ) * ‖eulerProfile t p‖ := hmem.mul_left 4
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) h4
  have h2 := two_le_prime_cast p
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  have hone : (1 : ℝ) ≤ ((p : ℕ) : ℝ) ^ t := Real.one_le_rpow (by linarith) ht
  have hkey : 1 / (4 * ((p : ℕ) : ℝ)) ≤ ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [norm_eulerProfile]
  have hstep : (4 : ℝ) * (1 / (4 * ((p : ℕ) : ℝ))) = 1 / ((p : ℕ) : ℝ) := by
    field_simp
  calc (1 : ℝ) / ((p : ℕ) : ℝ) = 4 * (1 / (4 * ((p : ℕ) : ℝ))) := hstep.symm
    _ ≤ 4 * (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ ≤ 4 * (((p : ℕ) : ℝ) ^ t * ((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) + 1) ^ 2) := by
        have hnum : ((p : ℕ) : ℝ) ≤ ((p : ℕ) : ℝ) ^ t * ((p : ℕ) : ℝ) :=
          le_mul_of_one_le_left (le_of_lt hp0) hone
        gcongr

/-- **Card `(RRC.13)`.**  The physical class of the Euler profile. -/
noncomputable def eulerClass (t : ℝ) : physicalQuotient :=
  Submodule.Quotient.mk (eulerProfile t)

/-- **Card `(RRC.14)`, boxed.**  The physical class of the Euler profile is nonzero exactly at
and above the centre. -/
theorem eulerClass_ne_zero_iff (t : ℝ) : eulerClass t ≠ 0 ↔ 0 ≤ t := by
  rw [eulerClass, Ne, Submodule.Quotient.mk_eq_zero ellOnePrimes]
  constructor
  · intro h
    by_contra ht
    exact h (eulerProfile_mem_of_neg (lt_of_not_ge ht))
  · exact fun ht => eulerProfile_not_mem_of_nonneg ht

end PhysicalQuotient
/-! ## Forward and reflected physical characters -/

section PhysicalCharacter

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)
  {Nfam : ℤ → Type} [∀ n, AddCommGroup (Nfam n)] [∀ n, Module ℂ (Nfam n)]
  {X : ZCochain ℂ Nfam} (Φ : ZCochainMap S.complex X)

namespace RouteRSource

/-- **Card `(RRC.13)`.**  The forward physical character `[x] ↦ c_ρ · Ī_p([x]) · [F_{-t}]`. -/
@[reducible] noncomputable def forwardPhysChar (cρ : ℂ) (t : ℝ) :
    (A × ℂ) →ₗ[ℂ] physicalQuotient :=
  S.physChar cρ (eulerClass (-t))

/-- **Card `(RRC.13)`.**  The reflected physical character `[x] ↦ c_ρ · Ī_p([x]) · [F_t]`. -/
@[reducible] noncomputable def reflectedPhysChar (cρ : ℂ) (t : ℝ) :
    (A × ℂ) →ₗ[ℂ] physicalQuotient :=
  S.physChar cρ (eulerClass t)

end RouteRSource

/-- **Card `(RRC.14)`, `(RRC.31)`, boxed.**  The forward physical value of the retained class is
`c_ρ[F_{-t}]`, computed as an ordinary relative cone character. -/
theorem forward_retained_value (cρ : ℂ) (t : ℝ) (y : (coneComplex Φ).cocycles (-1))
    (hy : y.1.2 = S.eta) :
    coneCharacter Φ (-1) (S.forwardPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) ((coneComplex Φ).cls y)
      = cρ • eulerClass (-t) :=
  coneCharacter_retained S Φ cρ (eulerClass (-t)) y hy

/-- **Card `(RRC.14)`, `(RRC.31)`, boxed.**  The reflected physical value of the retained class is
`c_ρ[F_t]`. -/
theorem reflected_retained_value (cρ : ℂ) (t : ℝ) (y : (coneComplex Φ).cocycles (-1))
    (hy : y.1.2 = S.eta) :
    coneCharacter Φ (-1) (S.reflectedPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) ((coneComplex Φ).cls y)
      = cρ • eulerClass t :=
  coneCharacter_retained S Φ cρ (eulerClass t) y hy

/-- **Card `(RRC.14)`, boxed.**  The forward physical value is nonzero exactly at and below the
centre. -/
theorem forward_retained_ne_zero_iff {cρ : ℂ} (hc : cρ ≠ 0) (t : ℝ)
    (y : (coneComplex Φ).cocycles (-1)) (hy : y.1.2 = S.eta) :
    coneCharacter Φ (-1) (S.forwardPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) ((coneComplex Φ).cls y) ≠ 0
      ↔ t ≤ 0 := by
  rw [forward_retained_value S Φ cρ t y hy, smul_ne_zero_iff_right hc,
    eulerClass_ne_zero_iff, neg_nonneg]

/-- **Card `(RRC.14)`, boxed.**  The reflected physical value is nonzero exactly at and above the
centre. -/
theorem reflected_retained_ne_zero_iff {cρ : ℂ} (hc : cρ ≠ 0) (t : ℝ)
    (y : (coneComplex Φ).cocycles (-1)) (hy : y.1.2 = S.eta) :
    coneCharacter Φ (-1) (S.reflectedPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) ((coneComplex Φ).cls y) ≠ 0
      ↔ 0 ≤ t := by
  rw [reflected_retained_value S Φ cρ t y hy, smul_ne_zero_iff_right hc,
    eulerClass_ne_zero_iff]

/-- **Card `(RRC.14)`, boxed.**  Both physical values are nonzero exactly at the centre `t = 0`,
and at least one of them is nonzero for every `t`. -/
theorem retained_values_both_ne_zero_iff {cρ : ℂ} (hc : cρ ≠ 0) (t : ℝ)
    (y : (coneComplex Φ).cocycles (-1)) (hy : y.1.2 = S.eta) :
    (coneCharacter Φ (-1) (S.forwardPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) ((coneComplex Φ).cls y) ≠ 0
      ∧ coneCharacter Φ (-1) (S.reflectedPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) ((coneComplex Φ).cls y) ≠ 0)
      ↔ t = 0 := by
  rw [forward_retained_ne_zero_iff S Φ hc t y hy, reflected_retained_ne_zero_iff S Φ hc t y hy]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

end PhysicalCharacter

/-! ## The Route-R source datum is inhabited -/

section Witness

/-- **A nondegenerate Route-R source.**  On `ℂ²` the transport `(x,y) ↦ (x, y + x)`, the
augmentation `(x,y) ↦ x` and the regulator `(x,y) ↦ y` satisfy both Route-R axioms with a nonzero
augmentation, so the source datum is inhabited by a datum whose retained class is not carried by a
degenerate augmentation. -/
noncomputable def shearRouteRSource : RouteRSource (ℂ × ℂ) where
  α := LinearMap.prod (LinearMap.fst ℂ ℂ ℂ) (LinearMap.snd ℂ ℂ ℂ + LinearMap.fst ℂ ℂ ℂ)
  ε := LinearMap.fst ℂ ℂ ℂ
  reg := LinearMap.snd ℂ ℂ ℂ
  eps_alpha _ := rfl
  reg_comm x := by
    show (x.2 + x.1) - x.2 = x.1
    ring

theorem shearRouteRSource_eps_ne_zero : shearRouteRSource.ε ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) = 0 := congrArg (fun f => f ((1 : ℂ), (0 : ℂ))) h
  exact one_ne_zero h1

theorem shearRouteRSource_alpha_ne_id : shearRouteRSource.α ≠ LinearMap.id := by
  intro h
  have h1 : shearRouteRSource.α (1, 0) = ((1 : ℂ), (0 : ℂ)) := by
    rw [h, LinearMap.id_apply]
  have h2 : shearRouteRSource.α ((1 : ℂ), (0 : ℂ)) = ((1 : ℂ), (1 : ℂ)) := by
    refine Prod.ext rfl ?_
    show (0 : ℂ) + 1 = 1
    rw [zero_add]
  rw [h2] at h1
  exact one_ne_zero (congrArg Prod.snd h1)

end Witness

/-! ## The universal exactification and the literal Route-R values -/

section Exactification

namespace RouteRSource

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)

/-- **Card `(RRC.7)`, `(ROD.13)`.**  The retained source class is nonzero: the bilateral Stokes
regulator takes the value one on it. -/
theorem eta_class_ne_zero : S.complex.cls (n := 0) ⟨S.eta, S.eta_mem_cocycles⟩ ≠ 0 := by
  intro h
  have h1 : S.regulatorBar (S.complex.cls (n := 0) ⟨S.eta, S.eta_mem_cocycles⟩) = 1 :=
    S.regulatorBar_eta
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- The degree-zero differential of the exactification `A ⊕ ℂ → A ⊕ ℂ`, adjoining a primitive for
the retained class. -/
noncomputable def exactifyD₀ : (A × ℂ) →ₗ[ℂ] (A × ℂ) :=
  LinearMap.prod ((S.α - LinearMap.id).comp (LinearMap.fst ℂ A ℂ))
    (S.ε.comp (LinearMap.fst ℂ A ℂ) + LinearMap.snd ℂ A ℂ)

/-- The degree-one differential of the exactification, unchanged from the source. -/
noncomputable def exactifyD₁ : (A × ℂ) →ₗ[ℂ] ℂ := S.D₁

theorem exactifyD₁_comp_D₀ (x : A × ℂ) : S.exactifyD₁ (S.exactifyD₀ x) = 0 := by
  show S.ε (S.α x.1 - x.1) = 0
  rw [map_sub, S.eps_alpha, sub_self]

/-- **Card `(RRC.10)`.**  The resolved complex obtained from the source by adjoining a primitive
for the retained class. -/
noncomputable def exactifyComplex :
    ZCochain ℂ (fun n => (pieceCat (ModuleCat.of ℂ (A × ℂ)) (ModuleCat.of ℂ (A × ℂ))
      (ModuleCat.of ℂ ℂ) n : Type)) :=
  truncComplex S.exactifyD₀ S.exactifyD₁ S.exactifyD₁_comp_D₀

/-- **Card `(RRC.10)`.**  The strict comparison from the source into its exactification. -/
noncomputable def exactifyMap : ZCochainMap S.complex S.exactifyComplex where
  f
    | 0 => LinearMap.inl ℂ A ℂ
    | 1 => LinearMap.id
    | 2 => LinearMap.id
    | Int.ofNat (_ + 3) => 0
    | Int.negSucc _ => 0
  comm n x := by
    match n with
    | 0 =>
      refine Prod.ext ?_ ?_
      · rfl
      · show S.ε x = S.ε x + 0
        rw [add_zero]
    | 1 => rfl
    | 2 => rfl
    | Int.ofNat (_ + 3) => rfl
    | Int.negSucc 0 =>
      show (LinearMap.inl ℂ A ℂ) ((0 : (pieceCat (ModuleCat.of ℂ A) (ModuleCat.of ℂ (A × ℂ))
          (ModuleCat.of ℂ ℂ) (Int.negSucc 0) : Type) →ₗ[ℂ] A) x) = _
      rw [LinearMap.zero_apply, map_zero]
      exact (map_zero _).symm
    | Int.negSucc (_ + 1) => rfl

set_option linter.unusedVariables false in
/-- **Card `(RRC.11)`.**  The adjoined primitive `L = (0, 1)`. -/
noncomputable def exactifyPrimitive (S : RouteRSource A) : (A × ℂ) := (0, 1)

/-- **Card `(RRC.11)`.**  The comparison carries the retained class to the coboundary of the
adjoined primitive. -/
theorem exactify_comm_eta :
    S.exactifyMap.f 1 S.eta = S.exactifyComplex.d 0 S.exactifyPrimitive := by
  refine Prod.ext ?_ ?_
  · show (0 : A) = S.α 0 - 0
    rw [map_zero, sub_zero]
  · show (1 : ℂ) = S.ε 0 + 1
    rw [map_zero, zero_add]

/-- **Card `(ROD.13)`.**  The retained class dies in the exactification. -/
theorem exactify_cohomologyMap_eta :
    S.exactifyMap.cohomologyMap 0 (S.complex.cls ⟨S.eta, S.eta_mem_cocycles⟩) = 0 := by
  rw [ZCochainMap.cohomologyMap_cls, ZCochain.cls_eq_zero_iff]
  exact ⟨S.exactifyPrimitive, S.exactify_comm_eta.symm⟩

/-- **Card `(ROD.14a)`.**  The relative cone class `κ = (L, η)`. -/
theorem exactify_cone_cocycle :
    ((S.exactifyPrimitive, S.eta) :
        (fun n => (pieceCat (ModuleCat.of ℂ (A × ℂ)) (ModuleCat.of ℂ (A × ℂ))
          (ModuleCat.of ℂ ℂ) n : Type)) (-1 + 1) × (A × ℂ))
      ∈ (coneComplex S.exactifyMap).cocycles (-1) :=
  cone_cocycle_of_primitive S S.exactifyMap S.exactifyPrimitive S.exactify_comm_eta

/-- **Card `(ROD.14a)`.**  The relative cone class as a cohomology class. -/
noncomputable def exactifyConeClass : (coneComplex S.exactifyMap).cohomology (-1) :=
  (coneComplex S.exactifyMap).cls ⟨_, S.exactify_cone_cocycle⟩

/-- **Card `(ROD.14)`.**  The cone class projects onto the retained source class. -/
theorem exactify_conePr_coneClass :
    conePr S.exactifyMap (-1) S.exactifyConeClass
      = S.complex.cls ⟨S.eta, S.eta_mem_cocycles⟩ := rfl

/-- **Card `(ROD.17)`, boxed.**  The forward physical value of the relative cone class is
`c_ρ[F_{-t}]`. -/
theorem exactify_forward_value (cρ : ℂ) (t : ℝ) :
    coneCharacter S.exactifyMap (-1) (S.forwardPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) S.exactifyConeClass
      = cρ • eulerClass (-t) :=
  forward_retained_value S S.exactifyMap cρ t ⟨_, S.exactify_cone_cocycle⟩ rfl

/-- **Card `(ROD.18)`, boxed.**  The reflected physical value of the relative cone class is
`c_ρ[F_t]`. -/
theorem exactify_reflected_value (cρ : ℂ) (t : ℝ) :
    coneCharacter S.exactifyMap (-1) (S.reflectedPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) S.exactifyConeClass
      = cρ • eulerClass t :=
  reflected_retained_value S S.exactifyMap cρ t ⟨_, S.exactify_cone_cocycle⟩ rfl

/-- **Card `(ROD.17)`, `§6`.**  The forward physical value is nonzero exactly for `t ≤ 0`. -/
theorem exactify_forward_ne_zero_iff {cρ : ℂ} (hc : cρ ≠ 0) (t : ℝ) :
    coneCharacter S.exactifyMap (-1) (S.forwardPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) S.exactifyConeClass ≠ 0
      ↔ t ≤ 0 :=
  forward_retained_ne_zero_iff S S.exactifyMap hc t ⟨_, S.exactify_cone_cocycle⟩ rfl

/-- **Card `(ROD.18)`, `§6`.**  The reflected physical value is nonzero exactly for `0 ≤ t`. -/
theorem exactify_reflected_ne_zero_iff {cρ : ℂ} (hc : cρ ≠ 0) (t : ℝ) :
    coneCharacter S.exactifyMap (-1) (S.reflectedPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) S.exactifyConeClass ≠ 0
      ↔ 0 ≤ t :=
  reflected_retained_ne_zero_iff S S.exactifyMap hc t ⟨_, S.exactify_cone_cocycle⟩ rfl

/-- **Card `§6`, boxed.**  Forward and reflected physical values of the relative cone class are
simultaneously nonzero exactly at the centre `t = 0`. -/
theorem exactify_both_ne_zero_iff {cρ : ℂ} (hc : cρ ≠ 0) (t : ℝ) :
    (coneCharacter S.exactifyMap (-1) (S.forwardPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) S.exactifyConeClass ≠ 0
      ∧ coneCharacter S.exactifyMap (-1) (S.reflectedPhysChar cρ t)
        (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) S.exactifyConeClass ≠ 0)
      ↔ t = 0 :=
  retained_values_both_ne_zero_iff S S.exactifyMap hc t ⟨_, S.exactify_cone_cocycle⟩ rfl

/-- **Card `§6`, boxed reading.**  At the divisor parameter `t_ρ = 2 Re ρ − 1` the forward and
reflected physical values of the relative cone class are simultaneously nonzero exactly when `ρ`
lies on the critical line.  This is the card's RH-equivalence statement made literal: it fixes what
"simultaneous nonvanishing on the distinguished retained class" says about `ρ`, and proves nothing
about which `ρ` occur. -/
theorem exactify_both_ne_zero_iff_critical {cρ : ℂ} (hc : cρ ≠ 0) (ρ : ℂ) :
    (coneCharacter S.exactifyMap (-1) (S.forwardPhysChar cρ (2 * ρ.re - 1))
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (-(2 * ρ.re - 1))) b) S.exactifyConeClass ≠ 0
      ∧ coneCharacter S.exactifyMap (-1) (S.reflectedPhysChar cρ (2 * ρ.re - 1))
        (fun b => S.physChar_comp_D₀ cρ (eulerClass (2 * ρ.re - 1)) b) S.exactifyConeClass ≠ 0)
      ↔ ρ.re = 1 / 2 := by
  rw [exactify_both_ne_zero_iff S hc (2 * ρ.re - 1)]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

end RouteRSource

end Exactification

/-! ## The relative class is nonzero, and no orientation descends absolutely -/

section RelativeNoGo

namespace RouteRSource

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)

/-- **Card `(RRC.21)`.**  The relative cone class is nonzero.  A degree-zero cone boundary has
source coordinate a source coboundary, and the retained class is not one. -/
theorem exactifyConeClass_ne_zero : S.exactifyConeClass ≠ 0 :=
  cone_cls_ne_zero_of_conePr_ne_zero S.exactifyMap (-1) ⟨_, S.exactify_cone_cocycle⟩
    S.eta_class_ne_zero

end RouteRSource

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)
  {Nfam : ℤ → Type} [∀ n, AddCommGroup (Nfam n)] [∀ n, Module ℂ (Nfam n)]
  {X : ZCochain ℂ Nfam} (Φ : ZCochainMap S.complex X)

/-- **Card `(RRC.23)`.**  A degree-one functional on the resolved complex that is a cochain map
into a complex concentrated in degree one annihilates the image of the retained class, because
that image is a coboundary of the adjoined primitive. -/
theorem orientation_vanishes_of_primitive {V : Type} [AddCommGroup V] [Module ℂ V]
    (Ψ : Nfam (0 + 1) →ₗ[ℂ] V) (hΨ : ∀ x : Nfam 0, Ψ (X.d 0 x) = 0)
    (L : Nfam 0) (hL : (Φ.f 1 S.eta : Nfam (0 + 1)) = X.d 0 L) :
    Ψ (Φ.f 1 S.eta) = 0 := by
  rw [hL]
  exact hΨ L

/-- **Card `(RRC.23)`, Theorem C.**  No such functional can agree with a nonzero physical
orientation on the retained class: the physical observer does not descend through resolved
absolute cohomology. -/
theorem no_orientation_factors {V : Type} [AddCommGroup V] [Module ℂ V]
    (Ψ : Nfam (0 + 1) →ₗ[ℂ] V) (hΨ : ∀ x : Nfam 0, Ψ (X.d 0 x) = 0)
    (L : Nfam 0) (hL : (Φ.f 1 S.eta : Nfam (0 + 1)) = X.d 0 L)
    (cρ : ℂ) (v : V) (hne : cρ • v ≠ 0)
    (hagree : Ψ (Φ.f 1 S.eta) = cρ • v) : False :=
  hne (hagree ▸ orientation_vanishes_of_primitive S Φ Ψ hΨ L hL)

namespace RouteRSource

/-- **Card `(RRC.23)`, forward orientation.**  At and below the centre the forward physical value
is nonzero, so it does not factor through the universal exactification. -/
theorem exactify_no_forward_orientation {cρ : ℂ} (hc : cρ ≠ 0) {t : ℝ} (ht : t ≤ 0)
    (Ψ : (A × ℂ) →ₗ[ℂ] physicalQuotient)
    (hΨ : ∀ x : (A × ℂ), Ψ (S.exactifyComplex.d 0 x) = 0)
    (hagree : Ψ (S.exactifyMap.f 1 S.eta) = cρ • eulerClass (-t)) : False := by
  refine no_orientation_factors S S.exactifyMap Ψ hΨ S.exactifyPrimitive S.exactify_comm_eta
    cρ (eulerClass (-t)) ?_ hagree
  rw [smul_ne_zero_iff_right hc, eulerClass_ne_zero_iff, neg_nonneg]
  exact ht

/-- **Card `(RRC.23)`, reflected orientation.**  At and above the centre the reflected physical
value is nonzero, so it does not factor through the universal exactification. -/
theorem exactify_no_reflected_orientation {cρ : ℂ} (hc : cρ ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (Ψ : (A × ℂ) →ₗ[ℂ] physicalQuotient)
    (hΨ : ∀ x : (A × ℂ), Ψ (S.exactifyComplex.d 0 x) = 0)
    (hagree : Ψ (S.exactifyMap.f 1 S.eta) = cρ • eulerClass t) : False := by
  refine no_orientation_factors S S.exactifyMap Ψ hΨ S.exactifyPrimitive S.exactify_comm_eta
    cρ (eulerClass t) ?_ hagree
  rw [smul_ne_zero_iff_right hc, eulerClass_ne_zero_iff]
  exact ht

end RouteRSource

end RelativeNoGo

/-! ## The two displayed degree-zero sequences -/

section DegreeZero

variable {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]

/-- A module placed in cochain degree zero, with the zero module in every other degree. -/
noncomputable def degreeZeroComplex (M₀ : Type) [AddCommGroup M₀] [Module ℂ M₀] :
    ZCochain ℂ (fun n => (pieceCat (ModuleCat.of ℂ M₀) (ModuleCat.of ℂ PUnit)
      (ModuleCat.of ℂ PUnit) n : Type)) :=
  truncComplex (0 : M₀ →ₗ[ℂ] PUnit) (0 : PUnit →ₗ[ℂ] PUnit) (fun _ => rfl)

theorem degreeZeroComplex_cohomology_one_eq_zero
    (z : (degreeZeroComplex M₀).cohomology 0) : z = 0 := by
  obtain ⟨c, rfl⟩ := (degreeZeroComplex M₀).cls_surjective 0 z
  haveI : Subsingleton ((pieceCat (ModuleCat.of ℂ M₀) (ModuleCat.of ℂ PUnit)
      (ModuleCat.of ℂ PUnit) (0 + 1)) : Type) := inferInstanceAs (Subsingleton PUnit)
  have hc : c = 0 := Subtype.ext (Subsingleton.elim _ _)
  rw [hc, ZCochain.cls]
  exact Submodule.Quotient.mk_zero _

/-- **Card `(RRC.24)`, `(RRC.25)`, Theorem D.**  Every linear map from the degree-zero cohomology
of a degree-zero complex into the degree-one cohomology of another vanishes: both displayed short
exact sequences have zero connecting homomorphism into degree one. -/
theorem degreeZero_connecting_eq_zero {N₀ : Type} [AddCommGroup N₀] [Module ℂ N₀]
    (δ : (degreeZeroComplex N₀).cohomology (-1) →ₗ[ℂ] (degreeZeroComplex M₀).cohomology 0) :
    δ = 0 :=
  LinearMap.ext fun z => degreeZeroComplex_cohomology_one_eq_zero (δ z)

end DegreeZero

section Sequences

variable {E : Type} [AddCommGroup E] [Module ℂ E]

/-- **Card `(RRC.24)`.**  A regulator taking the value one on a vector is split by the line it
spans: `c ↦ c • e` is a section. -/
theorem regulator_section (π : E →ₗ[ℂ] ℂ) (e : E) (he : π e = 1) (c : ℂ) :
    π (c • e) = c := by
  rw [map_smul, he, smul_eq_mul, mul_one]

/-- **Card `(RRC.24)`.**  The variable-ideal extension splits: kernel and section line are
complementary. -/
theorem isCompl_ker_span (π : E →ₗ[ℂ] ℂ) (e : E) (he : π e = 1) :
    IsCompl (LinearMap.ker π) (ℂ ∙ e) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro x hx hspan
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hspan
    have h0 : π (c • e) = 0 := hx
    rw [regulator_section π e he] at h0
    rw [h0, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (x - π x • e) + π x • e := by abel
    rw [hx]
    refine Submodule.add_mem_sup ?_ (Submodule.mem_span_singleton.mpr ⟨π x, rfl⟩)
    show π (x - π x • e) = 0
    rw [map_sub, regulator_section π e he, sub_self]

/-- **Card `(RRC.25)`.**  The fixed physical sequence `0 → ℓ¹(𝒫) → ℂ^𝒫 → V → 0` is exact. -/
theorem ellOnePrimes_range_eq_ker :
    LinearMap.range ellOnePrimes.subtype = LinearMap.ker ellOnePrimes.mkQ := by
  rw [Submodule.range_subtype, Submodule.ker_mkQ]

end Sequences

namespace RouteRSource

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A)

/-- **Card `(RRC.25)`.**  The physical map is a nonzero direct coefficient multiplication, so it is
not the connecting homomorphism of either displayed degree-zero sequence, all of which vanish. -/
theorem physChar_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] (cρ : ℂ) (v : V)
    (h : cρ • v ≠ 0) : S.physChar cρ v ≠ 0 := by
  intro hz
  refine h ?_
  rw [← S.physChar_eta cρ v, hz, LinearMap.zero_apply]

/-- **Card `(RRC.35)`, boxed — the exact positive survivor.**  The universal exactification carries
a nonzero relative cone class, and the two ordinary cone characters evaluate on it to the forward
and reflected physical Cartier classes, which are simultaneously nonzero exactly at the centre. -/
theorem routeR_positive_survivor {cρ : ℂ} (hc : cρ ≠ 0) (t : ℝ) :
    S.exactifyConeClass ≠ 0
      ∧ coneCharacter S.exactifyMap (-1) (S.forwardPhysChar cρ t)
          (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) S.exactifyConeClass
        = cρ • eulerClass (-t)
      ∧ coneCharacter S.exactifyMap (-1) (S.reflectedPhysChar cρ t)
          (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) S.exactifyConeClass
        = cρ • eulerClass t
      ∧ ((coneCharacter S.exactifyMap (-1) (S.forwardPhysChar cρ t)
            (fun b => S.physChar_comp_D₀ cρ (eulerClass (-t)) b) S.exactifyConeClass ≠ 0
          ∧ coneCharacter S.exactifyMap (-1) (S.reflectedPhysChar cρ t)
            (fun b => S.physChar_comp_D₀ cρ (eulerClass t) b) S.exactifyConeClass ≠ 0)
        ↔ t = 0) :=
  ⟨S.exactifyConeClass_ne_zero, S.exactify_forward_value cρ t, S.exactify_reflected_value cρ t,
    S.exactify_both_ne_zero_iff hc t⟩

end RouteRSource

end RouteR

end HTGeometry.ConstraintRelativity
