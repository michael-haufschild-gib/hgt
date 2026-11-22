import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.Coercivity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.NormalForm

/-! # A uniform commutator inverse on transverse perturbations of a separator -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.Separator
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev M := Matrix I I ℂ
private abbrev bracket (A : M) := UntouchedSites.bracket A
private def anti (Q : M) : M →ₗ[ℂ] M := LinearMap.mulLeft ℂ Q+LinearMap.mulRight ℂ Q

/-- A diagonal generator with simple levels has no commuting matrix
which anticommutes with a diagonal separator of nonzero entries. -/
private theorem seed_coercivity (d q : I→ℂ) (hd : Function.Injective d) (hq : ∀ i, q i≠0) :
    ∃ K > (0:ℝ), ∀ X : M, ‖X‖ ≤ K*max ‖diagonal d*X-X*diagonal d‖ ‖diagonal q*X+X*diagonal q‖ := by
  let F := (bracket (diagonal d)).prod (anti (diagonal q))
  have hk : F.ker=⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro X h
    have hc : diagonal d*X=X*diagonal d := sub_eq_zero.mp (congrArg Prod.fst h)
    have ha : diagonal q*X+X*diagonal q=0 := congrArg Prod.snd h
    ext i j
    change X i j=0
    by_cases hij : i=j
    · subst j
      have he := congrArg (fun A : M => A i i) ha
      simp only [Matrix.add_apply,diagonal_mul,mul_diagonal,Matrix.zero_apply] at he
      exact (mul_eq_zero.mp (show q i*X i i=0 by linear_combination he/2)).resolve_left (hq i)
    · have he := congrArg (fun A : M => A i j) hc
      simp only [diagonal_mul,mul_diagonal] at he
      exact (mul_eq_zero.mp (show (d i-d j)*X i j=0 by linear_combination he)).resolve_left
        (sub_ne_zero.mpr (hd.ne hij))
  obtain ⟨K,hK,h⟩ := F.exists_antilipschitzWith hk
  refine ⟨K,by exact_mod_cast hK,fun X => ?_⟩
  have h' := h.le_mul_dist X 0
  rw [map_zero,dist_zero_right,dist_zero_right] at h'
  exact h'

private theorem bracket_bound (B X : M) : ‖B*X-X*B‖ ≤ 2*‖B‖*‖X‖ := by
  apply (norm_sub_le _ _).trans
  calc _ ≤ ‖B‖*‖X‖+‖X‖*‖B‖ := add_le_add (norm_mul_le ..) (norm_mul_le ..)
       _ = _ := by ring

private theorem anti_bound (B X : M) : ‖B*X+X*B‖ ≤ 2*‖B‖*‖X‖ := by
  apply (norm_add_le _ _).trans
  calc _ ≤ ‖B‖*‖X‖+‖X‖*‖B‖ := add_le_add (norm_mul_le ..) (norm_mul_le ..)
       _ = _ := by ring

/-- For commuting H,Q near a simple diagonal reference, [H,·] maps the
matrices anticommuting with Q bijectively onto themselves, with uniformly
bounded inverse. Only injectivity at the reference enters the estimate. -/
theorem transverse_inverse (d q : I→ℂ) (hd : Function.Injective d) (hq : ∀ i, q i≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ H Q : M, ‖diagonal d-H‖ ≤ r → ‖diagonal q-Q‖ ≤ r →
      H*Q=Q*H → ∀ V : M, Q*V+V*Q=0 → ∃ X : M, H*X-X*H=V ∧ ‖X‖ ≤ C*‖V‖ := by
  obtain ⟨K,hK,hbase⟩ := seed_coercivity d q hd hq
  let r := 1/(4*K)
  have hr : 0<r := by dsimp only [r]; positivity
  refine ⟨r,2*K,hr,mul_pos two_pos hK,?_⟩
  intro H Q hH hQ hcom
  have bound (X : M) (hx : Q*X+X*Q=0) : ‖X‖ ≤ (2*K)*‖H*X-X*H‖ := by
    have hs : ‖diagonal d*X-X*diagonal d‖ ≤ ‖H*X-X*H‖+2*r*‖X‖ := by
      have he : diagonal d*X-X*diagonal d=(H*X-X*H)+((diagonal d-H)*X-X*(diagonal d-H)) := by noncomm_ring
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add_left ((bracket_bound _ _).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by norm_num)) (norm_nonneg X))) _)
    have ha : ‖diagonal q*X+X*diagonal q‖ ≤ 2*r*‖X‖ := by
      have he : diagonal q*X+X*diagonal q=((diagonal q-Q)*X+X*(diagonal q-Q))+(Q*X+X*Q) := by noncomm_ring
      rw [he,hx,add_zero]
      exact (anti_bound _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by norm_num)) (norm_nonneg X))
    have h := (hbase X).trans (mul_le_mul_of_nonneg_left
      (max_le hs (ha.trans (le_add_of_nonneg_left (norm_nonneg _)))) hK.le)
    have he : K*(2*r)=1/2 := by dsimp only [r]; field_simp
    rw [mul_add,←mul_assoc,he] at h
    linarith only [h]
  let O := (anti Q).ker
  let F : O →ₗ[ℂ] O := ((bracket H).comp O.subtype).codRestrict O (by
    intro x
    change Q*(H*x.val-x.val*H)+(H*x.val-x.val*H)*Q=0
    calc _ = H*(Q*x.val+x.val*Q)-(Q*x.val+x.val*Q)*H := by
             simp only [mul_add,add_mul,mul_sub,sub_mul,mul_assoc]
             rw [←mul_assoc Q H,←hcom,mul_assoc H Q,hcom]
             abel
         _ = 0 := by rw [show Q*x.val+x.val*Q=0 from x.property,mul_zero,zero_mul,sub_zero])
  have hker : F.ker=⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply norm_le_zero_iff.mp
    have hh := bound x.val x.property
    have he : H*x.val-x.val*H=0 := congrArg Subtype.val hx
    rwa [he,norm_zero,mul_zero] at hh
  intro V hV
  obtain ⟨X,hX⟩ := (LinearMap.surjective_of_injective F (LinearMap.ker_eq_bot.mp hker)) (⟨V,hV⟩ : O)
  have he : H*X.val-X.val*H=V := congrArg Subtype.val hX
  exact ⟨X.val,he,he ▸ bound X.val X.property⟩

#print axioms transverse_inverse

/-- A transverse term of size δ changes the entire evolution by at most
Cδ(2+|t|δ). The same constant works throughout the diagonal neighborhood. -/
theorem transverse_evolution (d q : I→ℂ) (hd : Function.Injective d) (hq : ∀ i, q i≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ H Q V : M, ‖diagonal d-H‖ ≤ r → ‖diagonal q-Q‖ ≤ r →
      IsSelfAdjoint H → IsSelfAdjoint V → H*Q=Q*H → Q*V+V*Q=0 → ∀ t : ℝ,
      ‖NormedSpace.exp (t • ((-Complex.I) • (H+V)))-NormedSpace.exp (t • ((-Complex.I) • H))‖ ≤
        C*‖V‖*(2+|t|*‖V‖) := by
  letI : CStarAlgebra M := {}
  obtain ⟨r,C,hr,hC,h⟩ := transverse_inverse d q hd hq
  refine ⟨r,C,hr,hC,?_⟩
  intro H Q V hH hQ hself hv hcom hodd t
  obtain ⟨X,he,hX⟩ := h H Q hH hQ hcom V hodd
  have hb := Dephasing.field_evolution_bound H V 0 X hself hv (isSelfAdjoint_zero _) (by simpa only [sub_zero] using he) 1 t
  simp only [one_smul,add_zero,abs_one,mul_one,one_pow,mul_zero,zero_sub,norm_neg] at hb
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_left ((norm_mul_le V X).trans (mul_le_mul_of_nonneg_left hX (norm_nonneg _))) (abs_nonneg t)
  linarith only [hm,mul_le_mul_of_nonneg_left hX (by norm_num : (0:ℝ) ≤ 2)]

#print axioms transverse_evolution
end
end GaloisForLFunctions.HTGeometry.WeakBonds.Separator
