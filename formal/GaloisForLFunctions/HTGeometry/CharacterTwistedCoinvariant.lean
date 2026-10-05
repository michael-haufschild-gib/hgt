import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Group.AddChar
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Character-twisted coinvariants of a monoid algebra

Let `M` be a commutative monoid, `k` a field and `χ : M → k` a character.  On `k[M] = M →₀ k` the
regular action is `ρ(a) e_m = e_{a+m}`, the twisted submodule is
`N_χ = span {ρ(a) v - χ(a) v}` and the character reporter is `τ_χ(Σ a_m e_m) = Σ a_m χ(m)`
`(CTL.2)`–`(CTL.4)`.

Then `ker τ_χ = N_χ` and `k[M]/N_χ ≃ k` `(CTL.5)`: multiplicativity of `χ` puts the generators in
the kernel, and `v - τ_χ(v) e_0 = Σ_m a_m (ρ(m) e_0 - χ(m) e_0) ∈ N_χ`.  A functional is
`χ`-covariant, `τ ∘ ρ(a) = χ(a) τ`, exactly when it kills `N_χ`, i.e. factors through the twisted
quotient, i.e. is a multiple of `τ_χ` `(CTL.6)`.

For `M = ℕ^d` every character is `χ_z(m) = Π_i z_i^{m_i}`, its reporter is polynomial evaluation at
`z`, and the family of all characters is coefficient-faithful.  In contrast, no single functional
is injective on an infinite-dimensional space.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.CharacterCoinvariant

variable {M k : Type*} [AddCommMonoid M] [Field k]

/-- The regular action `ρ(a) e_m = e_{a+m}` `(CTL.2)`. -/
def regularAction (a : M) : (M →₀ k) →ₗ[k] (M →₀ k) := Finsupp.lmapDomain k k (a + ·)

theorem regularAction_single (a m : M) (c : k) :
    regularAction a (Finsupp.single m c) = Finsupp.single (a + m) c :=
  Finsupp.mapDomain_single

variable (χ : AddChar M k)

/-- The character reporter `τ_χ(Σ a_m e_m) = Σ a_m χ(m)` `(CTL.4)`. -/
def charReporter : (M →₀ k) →ₗ[k] k := Finsupp.linearCombination k fun m => χ m

/-- The twisted submodule `N_χ = span {ρ(a) v - χ(a) v}` `(CTL.3)`. -/
def twistedSubmodule : Submodule k (M →₀ k) :=
  Submodule.span k {w | ∃ a v, w = regularAction a v - χ a • v}

theorem charReporter_single (m : M) (c : k) : charReporter χ (Finsupp.single m c) = c * χ m := by
  rw [charReporter, Finsupp.linearCombination_single, smul_eq_mul]

/-- `τ_χ ∘ ρ(a) = χ(a) τ_χ`. -/
theorem charReporter_regularAction (a : M) (v : M →₀ k) :
    charReporter χ (regularAction a v) = χ a * charReporter χ v := by
  rw [charReporter, regularAction, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  have : ((fun m => χ m) ∘ (a + ·)) = fun m => χ a * χ m := funext fun m => by
    simp [AddChar.map_add_eq_mul]
  rw [this, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [smul_eq_mul]
  ring

theorem sub_charReporter_mem (v : M →₀ k) :
    v - charReporter χ v • Finsupp.single 0 1 ∈ twistedSubmodule χ := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, add_smul, show f + g - (charReporter χ f • Finsupp.single 0 1 +
      charReporter χ g • Finsupp.single 0 1) = (f - charReporter χ f • Finsupp.single 0 1) +
        (g - charReporter χ g • Finsupp.single 0 1) by abel]
    exact add_mem hf hg
  | single m c =>
    rw [charReporter_single]
    have hgen : regularAction m (Finsupp.single 0 (1 : k)) - χ m • Finsupp.single 0 1 ∈
        twistedSubmodule χ := Submodule.subset_span ⟨m, _, rfl⟩
    rw [regularAction_single, add_zero] at hgen
    have := Submodule.smul_mem _ c hgen
    rwa [smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one, smul_smul] at this

/-- **Theorem 2.1, `(CTL.5)`**: `ker τ_χ = N_χ`. -/
theorem ker_charReporter : LinearMap.ker (charReporter χ) = twistedSubmodule χ := by
  refine le_antisymm (fun v hv => ?_) ((Submodule.span_le).2 ?_)
  · have h := sub_charReporter_mem χ v
    rwa [LinearMap.mem_ker.1 hv, zero_smul, sub_zero] at h
  · rintro _ ⟨a, v, rfl⟩
    simp [charReporter_regularAction]

theorem charReporter_surjective : Function.Surjective (charReporter χ) := fun c =>
  ⟨Finsupp.single 0 c, by rw [charReporter_single, AddChar.map_zero_eq_one, mul_one]⟩

/-- **Theorem 2.1, `(CTL.5)`**: the twisted quotient `k[M]/N_χ ≃ k`. -/
def twistedQuotientEquiv : ((M →₀ k) ⧸ twistedSubmodule χ) ≃ₗ[k] k :=
  (Submodule.quotEquivOfEq _ _ (ker_charReporter χ)).symm.trans
    ((charReporter χ).quotKerEquivOfSurjective (charReporter_surjective χ))

theorem twistedQuotientEquiv_mk (v : M →₀ k) :
    twistedQuotientEquiv χ (Submodule.Quotient.mk v) = charReporter χ v := rfl

/-- **`(CTL.6)`**: a functional is `χ`-covariant iff it kills `N_χ`, iff it factors through the
twisted quotient, iff it is a multiple of `τ_χ`. -/
theorem covariant_tfae (τ : (M →₀ k) →ₗ[k] k) :
    List.TFAE [∀ a v, τ (regularAction a v) = χ a * τ v,
      twistedSubmodule χ ≤ LinearMap.ker τ,
      ∃ τ' : ((M →₀ k) ⧸ twistedSubmodule χ) →ₗ[k] k, τ = τ' ∘ₗ (twistedSubmodule χ).mkQ,
      ∃ c : k, τ = c • charReporter χ] := by
  tfae_have 1 → 2 := fun h => (Submodule.span_le).2 fun w ⟨a, v, hw⟩ => by
    rw [SetLike.mem_coe, LinearMap.mem_ker, hw, map_sub, map_smul, h, smul_eq_mul, sub_self]
  tfae_have 2 → 3 := fun h => ⟨(twistedSubmodule χ).liftQ τ h, by
    ext v; simp⟩
  tfae_have 3 → 4 := fun ⟨τ', hτ⟩ => ⟨τ (Finsupp.single 0 1), by
    refine LinearMap.ext fun v => ?_
    have h := sub_charReporter_mem χ v
    have h0 : τ (v - charReporter χ v • Finsupp.single 0 1) = 0 := by
      rw [hτ, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 h,
        map_zero]
    rw [map_sub, map_smul, sub_eq_zero] at h0
    rw [h0, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]⟩
  tfae_have 4 → 1 := fun ⟨c, hc⟩ a v => by
    rw [hc, LinearMap.smul_apply, LinearMap.smul_apply, charReporter_regularAction, smul_eq_mul,
      smul_eq_mul]
    ring
  tfae_finish

/-! ### `M = ℕ^d`: the complete character spectrum -/

/-- The character `χ_z(m) = Π_i z_i^{m_i}` of `ℕ^d`. -/
def powChar {σ : Type*} (z : σ → k) : AddChar (σ →₀ ℕ) k where
  toFun m := m.prod fun i e => z i ^ e
  map_zero_eq_one' := Finsupp.prod_zero_index
  map_add_eq_mul' _ _ := Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

/-- Every character of `ℕ^d` is some `χ_z`, with `z_i = χ(e_i)`. -/
theorem eq_powChar {σ : Type*} (ψ : AddChar (σ →₀ ℕ) k) :
    ψ = powChar fun i => ψ (Finsupp.single i 1) := by
  ext m
  induction m using Finsupp.induction with
  | zero => simp [AddChar.map_zero_eq_one]
  | single_add i e m _ _ ih =>
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ih]
    congr 1
    simp only [powChar, AddChar.coe_mk]
    rw [Finsupp.prod_single_index (by simp), ← AddChar.map_nsmul_eq_pow, Finsupp.smul_single,
      smul_eq_mul, mul_one]

/-- The reporter of `χ_z` is polynomial evaluation at `z`. -/
theorem charReporter_powChar {σ : Type*} (z : σ → k) (v : (σ →₀ ℕ) →₀ k) :
    charReporter (powChar z) v = MvPolynomial.eval z (AddMonoidAlgebra.ofCoeff v) := by
  rw [MvPolynomial.eval_eq, charReporter, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [smul_eq_mul, powChar, AddChar.coe_mk, Finsupp.prod]
  rfl

/-- **Finite-support reconstruction**: on `k[ℕ^d]` over an infinite field the reporters of all
characters jointly determine every coefficient. -/
theorem eq_zero_of_forall_charReporter [Infinite k] {σ : Type*} (v : (σ →₀ ℕ) →₀ k)
    (h : ∀ ψ : AddChar (σ →₀ ℕ) k, charReporter ψ v = 0) : v = 0 := by
  have hp : (AddMonoidAlgebra.ofCoeff v : MvPolynomial σ k) = 0 := MvPolynomial.funext fun z => by
    rw [map_zero, ← charReporter_powChar]
    exact h _
  have := congrArg AddMonoidAlgebra.coeff hp
  simpa using this

/-- **Loop A**: a single functional is never injective on an infinite-dimensional space. -/
theorem not_injective_of_not_finiteDimensional {V : Type*} [AddCommGroup V] [Module k V]
    (hV : ¬ FiniteDimensional k V) (f : V →ₗ[k] k) : ¬ Function.Injective f := fun hf =>
  hV (Module.Finite.of_injective f hf)

end GaloisForLFunctions.HTGeometry.CharacterCoinvariant
