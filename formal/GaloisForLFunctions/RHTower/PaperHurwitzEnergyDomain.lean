import GaloisForLFunctions.RHTower.PaperHurwitzCompactCharacter

/-!
# Literal maximal energy domain of the Hurwitz history

The bounded regularizer is the genuine inverse of one plus the native, generally unbounded,
diagonal energy operator on its maximal square-summable domain. The range is exactly that
energy domain and is dense. Thus the compact-ideal calculation does not replace the source
energy by a surrogate bounded operator.
-/

namespace RHTower

noncomputable section
open Filter Classical GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Topology

/-- The maximal domain on which the literal power-energy product remains square summable. -/
def paperHurwitzEnergyDomain (rho : ℂ) : Submodule ℂ PaperHurwitzHistory where
  carrier := {u | Memℓp (fun k => (paperHurwitzPowerEnergy rho k : ℂ) * u k) 2}
  zero_mem' := by
    change Memℓp (fun k => (paperHurwitzPowerEnergy rho k : ℂ) * 0) 2
    simp only [mul_zero]
    change Memℓp (0 : ℕ → ℂ) 2
    exact zero_memℓp
  add_mem' := by
    intro u v hu hv
    change Memℓp (fun k => (paperHurwitzPowerEnergy rho k : ℂ) * (u k + v k)) 2
    have h := hu.add hv
    change Memℓp (fun k => (paperHurwitzPowerEnergy rho k : ℂ) * u k +
      (paperHurwitzPowerEnergy rho k : ℂ) * v k) 2 at h
    simpa only [mul_add] using h
  smul_mem' := by
    intro c u hu
    change Memℓp (fun k => (paperHurwitzPowerEnergy rho k : ℂ) * (c * u k)) 2
    have h := hu.const_smul c
    change Memℓp (fun k => c * ((paperHurwitzPowerEnergy rho k : ℂ) * u k)) 2 at h
    simpa only [mul_left_comm] using h

/-- The native energy acts without a cutoff on precisely its maximal domain. -/
def paperHurwitzEnergyOperator (rho : ℂ) : paperHurwitzEnergyDomain rho →ₗ[ℂ] PaperHurwitzHistory where
  toFun u := ⟨fun k => (paperHurwitzPowerEnergy rho k : ℂ) * u.1 k, u.2⟩
  map_add' := by intros; ext k; simp [mul_add]
  map_smul' := by intros; ext k; simp [mul_left_comm]

@[simp] theorem paperHurwitzEnergyOperator_apply (rho : ℂ)
    (u : paperHurwitzEnergyDomain rho) (k : ℕ) :
    paperHurwitzEnergyOperator rho u k = (paperHurwitzPowerEnergy rho k : ℂ) * u.1 k := rfl

private theorem regularizer_balance (rho : ℂ) (k : ℕ) :
    (paperHurwitzPowerEnergy rho k : ℂ) * (paperHurwitzRegularizer rho k : ℂ) =
      1 - (paperHurwitzRegularizer rho k : ℂ) := by
  have h : paperHurwitzPowerEnergy rho k * paperHurwitzRegularizer rho k =
      1 - paperHurwitzRegularizer rho k := by
    have hn : 1 + paperHurwitzPowerEnergy rho k ≠ 0 :=
      ne_of_gt (by linarith [paperHurwitzPowerEnergy_nonneg rho k])
    have hm := mul_inv_cancel₀ hn
    change (1 + paperHurwitzPowerEnergy rho k) * paperHurwitzRegularizer rho k = 1 at hm
    nlinarith only [hm]
  exact_mod_cast h

private theorem regularizer_inverse (rho : ℂ) (k : ℕ) :
    (paperHurwitzRegularizer rho k : ℂ) * (1 + (paperHurwitzPowerEnergy rho k : ℂ)) = 1 := by
  have hn : 1 + paperHurwitzPowerEnergy rho k ≠ 0 :=
    ne_of_gt (by linarith [paperHurwitzPowerEnergy_nonneg rho k])
  have hm := inv_mul_cancel₀ hn
  change paperHurwitzRegularizer rho k * (1 + paperHurwitzPowerEnergy rho k) = 1 at hm
  exact_mod_cast hm

/-- Every regularized full history lies in the actual maximal energy domain. -/
theorem paperHurwitzResolvent_mem_energyDomain (rho : ℂ) (f : PaperHurwitzHistory) :
    paperHurwitzResolvent rho f ∈ paperHurwitzEnergyDomain rho := by
  change Memℓp (fun k => (paperHurwitzPowerEnergy rho k : ℂ) *
    paperHurwitzResolvent rho f k) 2
  have heq : (fun k => (paperHurwitzPowerEnergy rho k : ℂ) *
      paperHurwitzResolvent rho f k) = fun k => (f - paperHurwitzResolvent rho f) k := by
    funext k
    simp only [paperHurwitzResolvent_apply, lp.coeFn_sub, Pi.sub_apply]
    rw [← mul_assoc, regularizer_balance, sub_mul, one_mul]
  rw [heq]
  exact lp.memℓp _

/-- Regularization with its maximal-domain certificate attached. -/
def paperHurwitzResolventDomain (rho : ℂ) (f : PaperHurwitzHistory) : paperHurwitzEnergyDomain rho :=
  ⟨paperHurwitzResolvent rho f, paperHurwitzResolvent_mem_energyDomain rho f⟩

/-- Exact energy-resolvent equation, as an equality of complete `ℓ²` histories. -/
theorem paperHurwitzEnergyOperator_resolvent (rho : ℂ) (f : PaperHurwitzHistory) :
    paperHurwitzEnergyOperator rho (paperHurwitzResolventDomain rho f) =
      f - paperHurwitzResolvent rho f := by
  ext k
  change (paperHurwitzPowerEnergy rho k : ℂ) *
    ((paperHurwitzRegularizer rho k : ℂ) * f k) =
      f k - (paperHurwitzRegularizer rho k : ℂ) * f k
  rw [← mul_assoc, regularizer_balance, sub_mul, one_mul]

/-- The inverse equation holds on every point of the maximal domain. -/
theorem paperHurwitzResolvent_energyOperator (rho : ℂ) (u : paperHurwitzEnergyDomain rho) :
    paperHurwitzResolvent rho (u.1 + paperHurwitzEnergyOperator rho u) = u.1 := by
  ext k
  let z : ℂ := u.1 k
  change (paperHurwitzRegularizer rho k : ℂ) *
    (z + (paperHurwitzPowerEnergy rho k : ℂ) * z) = z
  calc
    _ = ((paperHurwitzRegularizer rho k : ℂ) *
      (1 + (paperHurwitzPowerEnergy rho k : ℂ))) * z := by ring
    _ = z := by rw [regularizer_inverse, one_mul]

/-- The resolvent range is exactly the full native energy domain. -/
theorem paperHurwitzResolvent_range_iff (rho : ℂ) (u : PaperHurwitzHistory) :
    u ∈ Set.range (paperHurwitzResolvent rho) ↔ u ∈ paperHurwitzEnergyDomain rho := by
  constructor
  · rintro ⟨f, rfl⟩
    exact paperHurwitzResolvent_mem_energyDomain rho f
  · intro hu
    exact ⟨u + paperHurwitzEnergyOperator rho ⟨u, hu⟩,
      paperHurwitzResolvent_energyOperator rho ⟨u, hu⟩⟩

/-- The literal maximal-domain resolvent has dense range in the complete history space. -/
theorem paperHurwitzResolvent_denseRange (rho : ℂ) : DenseRange (paperHurwitzResolvent rho) := by
  intro y
  have hy := lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) y
  refine mem_closure_of_tendsto hy (Eventually.of_forall fun F => ?_)
  refine ⟨∑ i ∈ F, lp.single 2 i ((1 + (paperHurwitzPowerEnergy rho i : ℂ)) * y i), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [paperHurwitzResolvent_eq_diagonal, lpDiagonalCLM_single_apply,
    ← mul_assoc, regularizer_inverse]
  simp only [one_mul]

end
end RHTower
