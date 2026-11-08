import GaloisForLFunctions.RHTower.PrimeProductCutoffContraction

/-!
# Dirichlet gauges on prime-product chains

Multiplying a prime vertex by `p^s` conjugates the unweighted augmented boundary
to the Dirichlet boundary with coefficient `p^(-s)`. The inverse uses `-s`.
Each face keeps its support, so the conjugacy preserves every product cutoff.
This concerns algebraic chains; analytic completions require separate norm bounds.
-/

noncomputable section
open Finset
open RHTower
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.EffectiveScalingGeometry


/-- Multiply each prime basis vector by its Dirichlet gauge. -/
def dirichletVertexGauge (s : ℂ) : (Nat.Primes →₀ ℂ) →ₗ[ℂ] (Nat.Primes →₀ ℂ) :=
  Finsupp.linearCombination ℂ (fun p : Nat.Primes => Finsupp.single p ((p:ℂ)^s))

theorem dirichletVertexGauge_single (s : ℂ) (p : Nat.Primes) (c : ℂ) :
    dirichletVertexGauge s (Finsupp.single p c)=Finsupp.single p ((p:ℂ)^s*c) := by
  simp only [dirichletVertexGauge,Finsupp.linearCombination_single,Finsupp.smul_single,
    smul_eq_mul,mul_comm]

private theorem prime_cast_ne_zero (p : Nat.Primes) : (p:ℂ)≠0 := by
  exact_mod_cast p.property.ne_zero

theorem dirichletVertexGauge_add (s t : ℂ) :
    (dirichletVertexGauge s).comp (dirichletVertexGauge t)=dirichletVertexGauge (s+t) := by
  apply Finsupp.lhom_ext
  intro p c
  simp only [LinearMap.comp_apply,dirichletVertexGauge_single]
  rw [Complex.cpow_add _ _ (prime_cast_ne_zero p),mul_assoc]

theorem dirichletVertexGauge_zero : dirichletVertexGauge 0=LinearMap.id := by
  apply Finsupp.lhom_ext
  intro p c
  simp only [dirichletVertexGauge_single,Complex.cpow_zero,one_mul,LinearMap.id_apply]

/-- The induced diagonal gauge on the actual exterior chains. -/
def dirichletChainGauge (s : ℂ) (k : ℕ) : PrimeChainSpace ℂ k →ₗ[ℂ] PrimeChainSpace ℂ k :=
  exteriorPower.map k (dirichletVertexGauge s)

theorem dirichletChainGauge_add (s t : ℂ) (k : ℕ) :
    (dirichletChainGauge s k).comp (dirichletChainGauge t k)=dirichletChainGauge (s+t) k := by
  simp only [dirichletChainGauge,← exteriorPower.map_comp,dirichletVertexGauge_add]

theorem dirichletChainGauge_zero (k : ℕ) : dirichletChainGauge 0 k=LinearMap.id := by
  rw [dirichletChainGauge,dirichletVertexGauge_zero,exteriorPower.map_id]

/-- Face scaling leaves the prime support unchanged. -/
theorem dirichletChainGauge_atom (s : ℂ) {k : ℕ} (v : Fin k → Nat.Primes) :
    dirichletChainGauge s k (primeChainAtom ℂ v)=
      (∏ i, (v i:ℂ)^s) • primeChainAtom ℂ v := by
  unfold dirichletChainGauge primeChainAtom
  rw [exteriorPower.map_apply_ιMulti]
  have hf : dirichletVertexGauge s ∘ (fun i => Finsupp.single (v i) (1:ℂ)) =
      (fun i => (v i:ℂ)^s • Finsupp.single (v i) (1:ℂ)) := by
    funext i
    simp only [Function.comp_apply,dirichletVertexGauge_single,Finsupp.smul_single,
      smul_eq_mul,mul_one]
  rw [hf,AlternatingMap.map_smul_univ]

/-- Every finite product cutoff is invariant under the gauge. -/
theorem dirichletChainGauge_cutoff (s : ℂ) (k N : ℕ) :
    primeChainCutoff ℂ k N ≤ (primeChainCutoff ℂ k N).comap (dirichletChainGauge s k) := by
  apply Submodule.span_le.mpr
  rintro x ⟨v,hv,rfl⟩
  change dirichletChainGauge s k (primeChainAtom ℂ v)∈primeChainCutoff ℂ k N
  rw [dirichletChainGauge_atom]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,hv,rfl⟩)

theorem dirichletFunctional_comp_gauge (s : ℂ) :
    (dirichletPrimeChainFunctional s).comp (dirichletVertexGauge s)=primeChainAugmentation ℂ := by
  apply Finsupp.lhom_ext
  intro p c
  simp only [LinearMap.comp_apply,dirichletVertexGauge_single,
    dirichletPrimeChainFunctional,primeChainAugmentation,Finsupp.linearCombination_single,
    smul_eq_mul,mul_one]
  have hu : (p:ℂ)^s*(p:ℂ)^(-s)=1 := by
    rw [← Complex.cpow_add _ _ (prime_cast_ne_zero p),add_neg_cancel,Complex.cpow_zero]
  calc
    ((p:ℂ)^s*c)*(p:ℂ)^(-s)=((p:ℂ)^s*(p:ℂ)^(-s))*c := by ring
    _=c := by rw [hu,one_mul]

/-- Dirichlet weighting is an exact conjugacy of the actual reduced boundary. -/
theorem dirichletChainGauge_boundary (s : ℂ) (k : ℕ) :
    (dirichletPrimeChainBoundary k s).comp (dirichletChainGauge s (k+1))=
      (dirichletChainGauge s k).comp (primeChainBoundary ℂ k) :=
  physicalKoszulDifferential_natural k (dirichletVertexGauge s)
    (dirichletPrimeChainFunctional s) (primeChainAugmentation ℂ)
    (dirichletFunctional_comp_gauge s)

/-- The inverse gauge is obtained by negating the complex parameter. -/
def dirichletChainGaugeEquiv (s : ℂ) (k : ℕ) :
    PrimeChainSpace ℂ k ≃ₗ[ℂ] PrimeChainSpace ℂ k :=
  LinearEquiv.ofLinear (dirichletChainGauge s k) (dirichletChainGauge (-s) k)
    (by rw [dirichletChainGauge_add,add_neg_cancel,dirichletChainGauge_zero])
    (by rw [dirichletChainGauge_add,neg_add_cancel,dirichletChainGauge_zero])

/-- Restriction to a product cutoff, as a named linear map. -/
def dirichletCutoffGauge (s : ℂ) (k N : ℕ) :
    primeChainCutoff ℂ k N →ₗ[ℂ] primeChainCutoff ℂ k N :=
  (dirichletChainGauge s k).restrict
    (fun _x hx => dirichletChainGauge_cutoff s k N hx)

theorem dirichletCutoffGauge_add (s t : ℂ) (k N : ℕ) :
    (dirichletCutoffGauge s k N).comp (dirichletCutoffGauge t k N)=
      dirichletCutoffGauge (s+t) k N := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (dirichletChainGauge_add s t k) x.val

theorem dirichletCutoffGauge_zero (k N : ℕ) :
    dirichletCutoffGauge 0 k N=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (dirichletChainGauge_zero k) x.val

/-- The conjugacy restricts to each cutoff without enlarging its height. -/
def dirichletCutoffGaugeEquiv (s : ℂ) (k N : ℕ) :
    primeChainCutoff ℂ k N ≃ₗ[ℂ] primeChainCutoff ℂ k N :=
  LinearEquiv.ofLinear (dirichletCutoffGauge s k N) (dirichletCutoffGauge (-s) k N)
    (by rw [dirichletCutoffGauge_add,add_neg_cancel,dirichletCutoffGauge_zero])
    (by rw [dirichletCutoffGauge_add,neg_add_cancel,dirichletCutoffGauge_zero])

#print axioms dirichletChainGauge_boundary
#print axioms dirichletCutoffGaugeEquiv
end GaloisForLFunctions.EffectiveScalingGeometry
