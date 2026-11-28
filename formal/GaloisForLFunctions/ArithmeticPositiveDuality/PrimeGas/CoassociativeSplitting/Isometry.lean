import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # Arbitrary normalized splitting amplitudes on integer product shells -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting

open Finset GaloisForLFunctions.HTGeometry

abbrev Kernel := ℕ+ → ℕ+ → ℂ

def wave (F : Kernel) (f : ℕ+ → ℂ) (x : ℕ+ × ℕ+) := F x.1 x.2 * f (x.1*x.2)

def isometric (F : Kernel) := ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x,T f x=wave F f x

/-- Probability on a single input shell, indexed by the full two-copy basis. -/
def shell (F : Kernel) (n : ℕ+) (x : ℕ+ × ℕ+) : ℝ :=
  if x.1*x.2=n then ‖F x.1 x.2‖^2 else 0

def normalized (F : Kernel) := ∀ n, HasSum (shell F n) 1

private def mass (F : Kernel) (n : ℕ+) :=
  ∑ d : n.val.divisorsAntidiagonal, ‖F (divisorsAntidiagonalFactors n d).1 (divisorsAntidiagonalFactors n d).2‖^2

private theorem row (F : Kernel) (f : ℕ+ → ℂ) (n : ℕ+) :
    (∑' d : n.val.divisorsAntidiagonal, ‖wave F f (sigmaAntidiagonalEquivProd ⟨n,d⟩)‖^2) =
    mass F n * ‖f n‖^2 := by
  rw [tsum_fintype,mass,Finset.sum_mul]
  refine sum_congr rfl fun d _ => ?_
  let x := divisorsAntidiagonalFactors n d
  change ‖F x.1 x.2 * f (x.1*x.2)‖^2 = _
  rw [show x.1*x.2=n from PNat.coe_injective (divisorsAntidiagonalFactors_eq d),norm_mul,mul_pow]

/-- Distinct integer inputs have disjoint output shells. -/
private theorem norm_series (F : Kernel) (f : ℕ+ → ℂ) (r : ℝ) :
    HasSum (fun x => ‖wave F f x‖^2) r ↔ HasSum (fun n => mass F n * ‖f n‖^2) r := by
  rw [←sigmaAntidiagonalEquivProd.hasSum_iff]
  have hrow (n : ℕ+) := (hasSum_fintype
    (fun d : n.val.divisorsAntidiagonal => ‖wave F f (sigmaAntidiagonalEquivProd ⟨n,d⟩)‖^2)).summable.hasSum
  constructor
  · intro h
    exact h.sigma fun n => (row F f n) ▸ hrow n
  · intro h
    have hs : Summable ((fun x => ‖wave F f x‖^2) ∘ sigmaAntidiagonalEquivProd) := by
      apply (summable_sigma_of_nonneg fun _ => sq_nonneg _).mpr
      exact ⟨fun n => (hrow n).summable,by simpa only [Function.comp_apply,row] using h.summable⟩
    rw [←h.tsum_eq]
    convert hs.hasSum using 1
    rw [hs.tsum_sigma]
    simp only [Function.comp_apply,row]

private def basis (n : ℕ+) : Gas := lp.single 2 n (1:ℂ)

private theorem basis_norm (n : ℕ+) : ‖basis n‖=1 := by
  rw [basis,lp.norm_single (by norm_num : 0 < (2:ENNReal)),norm_one]

private theorem basis_shell (F : Kernel) (n : ℕ+) (x : ℕ+ × ℕ+) :
    ‖wave F (basis n) x‖^2=shell F n x := by
  by_cases e : x.1*x.2=n
  · simp [wave,shell,basis,lp.single_apply,e]
  · simp [wave,shell,basis,lp.single_apply,e]

private theorem shell_series (F : Kernel) (n : ℕ+) : HasSum (shell F n) (mass F n) := by
  have h : HasSum (fun m => mass F m * ‖basis n m‖^2) (mass F n) := by
    refine (hasSum_ite_eq n (mass F n)).congr_fun fun m => ?_
    by_cases e : m=n
    · subst m
      simp [basis,lp.single_apply]
    · simp [basis,lp.single_apply,e]
  exact ((norm_series F (basis n) _).mpr h).congr_fun fun x => (basis_shell F n x).symm

/-- Unit shell mass is necessary and sufficient for an isometry on the
whole occupation Hilbert space, including inputs with infinite support. -/
theorem isometric_iff (F : Kernel) : isometric F ↔ normalized F := by
  constructor
  · rintro ⟨T,hT⟩ n
    have h := (lp_summable_norm_sq (T (basis n))).hasSum
    rw [←lp_norm_sq_eq_tsum,T.norm_map,basis_norm,one_pow] at h
    exact h.congr_fun fun x => by rw [hT,basis_shell]
  · intro h
    have hm (n : ℕ+) : mass F n=1 := (shell_series F n).unique (h n)
    have normed (f : Gas) : HasSum (fun x => ‖wave F f x‖^2) (‖f‖^2) := by
      apply (norm_series F f _).mpr
      simpa only [hm,one_mul,lp_norm_sq_eq_tsum] using (lp_summable_norm_sq f).hasSum
    let image (f : Gas) : PairGas := ⟨wave F f,HilbertSchmidt.memℓp_of_sq (normed f).summable⟩
    let T : Gas →ₗᵢ[ℂ] PairGas := {
      toFun := image
      map_add' := fun f g => Subtype.ext (funext fun x => mul_add _ _ _)
      map_smul' := fun c f => Subtype.ext (funext fun x => by
        change F x.1 x.2 * (c * f (x.1*x.2)) = c * (F x.1 x.2 * f (x.1*x.2))
        ring)
      norm_map' := fun f => by
        change ‖image f‖=‖f‖
        have eqn : ‖image f‖^2=‖f‖^2 := (lp_norm_sq_eq_tsum (image f)).trans (normed f).tsum_eq
        nlinarith only [eqn,norm_nonneg (image f),norm_nonneg f] }
    exact ⟨T,fun _ _ => rfl⟩

#print axioms isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CoassociativeSplitting
