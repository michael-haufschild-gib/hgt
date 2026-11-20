import GaloisForLFunctions.GaloisTheoryOfZeros.TheLocalDiscriminantOfAHeatCollision
import GaloisForLFunctions.HTGeometry.CauchyBinet

/-!
# Lower discriminants of a heat collision

The q-row moment determinant of a cluster is the mean of squared
Vandermonde determinants over ordered q-tuples, with normalization q!.
Under the Hermite blow-up it has time order q choose 2 whenever the
cluster contains at least q sheets. Its leading coefficient is positive
and depends only on the collision multiplicity. In particular the two-row
determinant has a simple zero even at a collision of very high order.
-/

open Complex Finset Matrix Filter Topology Metric Set RHTower RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section

/-- Principal Hankel minor of the power sums of a finite family of nodes. -/
def clusterMomentMinor {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) (q : ℕ) : R :=
  (Matrix.of fun i j : Fin q => ∑ a : Fin m, v a^(i.val+j.val)).det

/-- Cauchy–Binet for every order, allowing repeated nodes and repeated indices. -/
theorem factorial_mul_clusterMomentMinor {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) (q : ℕ) :
    (q.factorial : R)*clusterMomentMinor v q =
      ∑ f : Fin q → Fin m, (vandermonde (fun j => v (f j))).det^2 := by
  let A : Matrix (Fin m) (Fin q) R := Matrix.of fun i j => v i^j.val
  have hM : (Matrix.of fun i j : Fin q => ∑ a : Fin m, v a^(i.val+j.val)) = A.transpose*A := by
    ext i j
    simp only [A,Matrix.of_apply,Matrix.mul_apply,Matrix.transpose_apply,pow_add]
  rw [clusterMomentMinor,hM,factorial_mul_det_mul]
  apply sum_congr rfl
  intro f _
  change ((vandermonde (fun j => v (f j))).transpose).det * _ = _
  rw [det_transpose,pow_two] <;> rfl

private theorem num_pairs (q : ℕ) : (∑ i : Fin q, (Finset.Ioi i).card) = q.choose 2 := by
  calc _ = ∑ i : Fin q, (Fin.revPerm i : Fin q).val := by
             apply sum_congr rfl
             intro i _
             rw [Fin.card_Ioi]
             change q-1-i.val = q-(i.val+1)
             omega
       _ = ∑ i : Fin q, i.val := Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl
       _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => k),sum_range_id,Nat.choose_two_right]

/-- Translation cancels and each pair of selected sheets supplies one squared scale. -/
theorem clusterMomentMinor_affine {R : Type*} [Field R] [CharZero R] {m : ℕ}
    (v : Fin m → R) (q : ℕ) (z s : R) :
    clusterMomentMinor (fun i => z+s*v i) q = (s^2)^(q.choose 2)*clusterMomentMinor v q := by
  have hf : (q.factorial : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero q)
  apply mul_left_cancel₀ hf
  rw [factorial_mul_clusterMomentMinor,mul_left_comm,factorial_mul_clusterMomentMinor,mul_sum]
  apply sum_congr rfl
  intro f _
  simp only [det_vandermonde,add_sub_add_left_eq_sub,←mul_sub,prod_mul_distrib,prod_const,
    prod_pow_eq_pow_sum,num_pairs,mul_pow,←pow_mul,Nat.mul_comm (q.choose 2) 2]

/-- A distinct real profile gives a strictly positive minor at every order up to
the number of sheets. Beyond that order every minor vanishes over either field. -/
theorem clusterMomentMinor_pos {m q : ℕ} (v : Fin m → ℝ) (hv : Function.Injective v) (hq : q ≤ m) :
    0 < clusterMomentMinor v q := by
  let f : Fin q → Fin m := Fin.castLE hq
  have hf : Function.Injective f := fun i j he => Fin.ext (congrArg Fin.val he)
  have h := sq_pos_of_ne_zero (det_vandermonde_ne_zero_iff.mpr (hv.comp hf))
  have hs := (sum_pos' (s := (univ : Finset (Fin q → Fin m)))
    (fun g _ => sq_nonneg ((vandermonde (fun j => v (g j))).det)) ⟨f,mem_univ _,h⟩)
  rw [←factorial_mul_clusterMomentMinor] at hs
  exact pos_of_mul_pos_right hs (by positivity)

theorem clusterMomentMinor_zero_of_lt {m q : ℕ} (v : Fin m → ℂ) (hq : m < q) :
    clusterMomentMinor v q = 0 := by
  apply (mul_eq_zero.mp (show (q.factorial : ℂ)*clusterMomentMinor v q = 0 from ?_)).resolve_left
    (by exact_mod_cast Nat.factorial_ne_zero q)
  rw [factorial_mul_clusterMomentMinor]
  apply sum_eq_zero
  intro f _
  have hn : ¬ Function.Injective f := fun h => hq.not_ge (by simpa using Fintype.card_le_of_injective f h)
  have hdet : (vandermonde (fun j => v (f j))).det = 0 := by
    by_contra h
    exact hn (fun a b he => (det_vandermonde_ne_zero_iff.mp h) (congrArg v he))
  rw [hdet,zero_pow two_ne_zero]

/-- Ordered real roots of the parabolic collision profile. -/
def orderedHeatProfileRoot (m : ℕ) : Fin m ≃o ↥(profileRoots m) :=
  (profileRoots m).orderIsoOfFin (card_profileRoots m)

/-- The Hermite coefficient of the minor is independent of time and collision location. -/
def hermiteMinorCoefficient (m q : ℕ) : ℝ :=
  clusterMomentMinor (fun i : Fin m => ((orderedHeatProfileRoot m i : profileRoots m) : ℝ)) q

theorem hermiteMinorCoefficient_pos {m q : ℕ} (hq : q ≤ m) : 0 < hermiteMinorCoefficient m q :=
  clusterMomentMinor_pos _ (fun _ _ h => (orderedHeatProfileRoot m).injective (Subtype.ext h)) hq

/-- The q-row determinant read from all m sheets through a collision. -/
def collisionMomentMinor (τ z : ℂ) (m q : ℕ) (s : ℂ) : ℂ :=
  clusterMomentMinor (fun i : Fin m => collisionZero τ z m ((orderedHeatProfileRoot m i : ℝ) : ℂ) s) q

private theorem analytic_minor {m : ℕ} (y : ℂ → Fin m → ℂ) (q : ℕ)
    (hy : ∀ i, AnalyticAt ℂ (fun s => y s i) 0) :
    AnalyticAt ℂ (fun s => clusterMomentMinor (y s) q) 0 := by
  have h (s : ℂ) : clusterMomentMinor (y s) q =
      (q.factorial:ℂ)⁻¹*(∑ f : Fin q → Fin m, (vandermonde (fun j => y s (f j))).det^2) := by
    rw [←factorial_mul_clusterMomentMinor,←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero q),one_mul]
  simp_rw [h,det_vandermonde]
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro f _
  exact (Finset.analyticAt_fun_prod _ fun i _ => Finset.analyticAt_fun_prod _ fun j _ =>
    (hy (f j)).sub (hy (f i))).pow _

private theorem cast_clusterMinor {m : ℕ} (v : Fin m → ℝ) (q : ℕ) :
    ((clusterMomentMinor v q : ℝ) : ℂ) = clusterMomentMinor (fun i => (v i : ℂ)) q := by
  change Complex.ofRealHom _ = _
  rw [clusterMomentMinor,RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply,clusterMomentMinor]

/-- Exact scaling and leading coefficient in the square-root time coordinate. -/
theorem IsCollision.momentMinor_factor {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) (q : ℕ) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ U 0 = (hermiteMinorCoefficient m q : ℂ) ∧
      ∀ s : ℂ, collisionMomentMinor τ z m q s = (s^2)^(q.choose 2)*U s := by
  let y (s : ℂ) (i : Fin m) := collisionBranch τ z m ((orderedHeatProfileRoot m i : ℝ) : ℂ) s
  have hy (i : Fin m) := collisionBranch_spec hc (heatModelFwd_profileRoot (orderedHeatProfileRoot m i).property)
  refine ⟨fun s => clusterMomentMinor (y s) q,analytic_minor y q (fun i => (hy i).1),?_,?_⟩
  · rw [hermiteMinorCoefficient,cast_clusterMinor]
    exact congrArg (fun v => clusterMomentMinor v q) (funext fun i => (hy i).2.1)
  · intro s
    exact clusterMomentMinor_affine (y s) q z s

private theorem root_neg {m : ℕ} {r : ℝ} (hr : r ∈ profileRoots m) : -r ∈ profileRoots m := by
  have h : heatModelFwd m (-(r:ℂ)) = 0 := by
    rw [heatModelFwd_neg,heatModelFwd_profileRoot hr,mul_zero]
  obtain ⟨a,ha,he⟩ := heatModelFwd_eq_zero_iff.mp h
  have he' : a = -r := Complex.ofReal_injective (by simpa using he)
  rwa [he'] at ha

private theorem even_minor {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) (q : ℕ) :
    ∀ᶠ s in 𝓝 0, collisionMomentMinor τ z m q (-s) = collisionMomentMinor τ z m q s := by
  let negRoot : ↥(profileRoots m) ≃ ↥(profileRoots m) :=
    ⟨fun r => ⟨-r.val,root_neg r.property⟩,fun r => ⟨-r.val,root_neg r.property⟩,
      fun r => Subtype.ext (neg_neg _),fun r => Subtype.ext (neg_neg _)⟩
  let e := (orderedHeatProfileRoot m).toEquiv.trans (negRoot.trans (orderedHeatProfileRoot m).toEquiv.symm)
  have hroot (i : Fin m) : ((orderedHeatProfileRoot m (e i) : ℝ) : ℂ) = -((orderedHeatProfileRoot m i : ℝ) : ℂ) := by
    simp [e,negRoot]
  have h (i : Fin m) : ∀ᶠ s in 𝓝 0, collisionZero τ z m ((orderedHeatProfileRoot m i : ℝ) : ℂ) (-s) =
      collisionZero τ z m ((orderedHeatProfileRoot m (e i) : ℝ) : ℂ) s := by
    rw [hroot]
    exact collisionZero_neg hc (heatModelFwd_profileRoot (orderedHeatProfileRoot m i).property)
  filter_upwards [Filter.eventually_all.mpr h] with s hs
  unfold collisionMomentMinor clusterMomentMinor
  congr 1
  ext i j
  simp only [Matrix.of_apply,hs]
  exact Equiv.sum_comp e _

/-- In ordinary complex time each lower determinant has order q choose 2.
Its normalized leading coefficient is the positive Hermite minor. -/
theorem IsCollision.exists_momentMinor_germ {τ z : ℂ} {m q : ℕ} (hc : IsCollision τ z m) (hq : q ≤ m) :
    ∃ D V : ℂ → ℂ, AnalyticAt ℂ D 0 ∧ AnalyticAt ℂ V 0 ∧ V 0 = (hermiteMinorCoefficient m q : ℂ) ∧
      (∀ w, D w = w^(q.choose 2)*V w) ∧
      (∀ᶠ s in 𝓝 0, D (s^2) = collisionMomentMinor τ z m q s) ∧
      analyticOrderAt D 0 = (q.choose 2 : ℕ∞) := by
  obtain ⟨U,hU,h₀,hfactor⟩ := hc.momentMinor_factor q
  have hev : ∀ᶠ s in 𝓝 0, U (-s) = U s := by
    filter_upwards [even_minor hc q] with s hs
    by_cases h : s=0
    · simp [h]
    · rw [hfactor,hfactor,neg_sq] at hs
      exact mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero _ h)) hs
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hU.eventually_analyticAt.and hev)
  obtain ⟨V,hV,hVs⟩ := Bottcher.exists_analytic_factor_of_even hR
    (fun s hs => (hball hs).1.differentiableAt.differentiableWithinAt) (fun s hs => (hball hs).2)
  have hV0 : AnalyticAt ℂ V 0 := hV.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (sq_pos_of_pos hR)))
  have hz : V 0 = (hermiteMinorCoefficient m q : ℂ) := by
    simpa using (hVs 0 (mem_ball_self hR)).trans h₀
  have hne : V 0 ≠ 0 := hz ▸ Complex.ofReal_ne_zero.mpr (hermiteMinorCoefficient_pos hq).ne'
  let D (w : ℂ) := w^(q.choose 2)*V w
  have hD : AnalyticAt ℂ D 0 := (analyticAt_id.pow _).mul hV0
  refine ⟨D,V,hD,hV0,hz,fun _ => rfl,?_,hD.analyticOrderAt_eq_natCast.mpr ⟨V,hV0,hne,by simp [D]⟩⟩
  filter_upwards [ball_mem_nhds (0:ℂ) hR] with s hs
  rw [hfactor,D,hVs s hs]

/-- The quadratic moment determinant has a simple zero in physical time at every
multiple collision. Its derivative is real and strictly positive. -/
theorem IsCollision.two_moment_derivative {τ z : ℂ} {m : ℕ} (hc : IsCollision τ z m) (hm : 2 ≤ m) :
    ∃ D : ℂ → ℂ, (∀ᶠ s in 𝓝 0, D (s^2) = collisionMomentMinor τ z m 2 s) ∧
      D 0 = 0 ∧ HasDerivAt D (hermiteMinorCoefficient m 2 : ℂ) 0 := by
  obtain ⟨D,V,_,hV,h₀,hD,he,_⟩ := hc.exists_momentMinor_germ hm
  have hf : D = fun w => w*V w := funext fun w => by simpa using hD w
  refine ⟨D,he,by simp [hf],?_⟩
  rw [hf,←h₀]
  simpa using (hasDerivAt_id (0:ℂ)).mul hV.differentiableAt.hasDerivAt


end

end GaloisForLFunctions.GaloisTheoryOfZeros
