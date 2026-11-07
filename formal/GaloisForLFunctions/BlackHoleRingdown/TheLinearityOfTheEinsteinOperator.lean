import GaloisForLFunctions.BlackHoleRingdown.TheVectorModesOfTheMetric

/-!
# The linearity of the Einstein operator

The linearized cosmological Einstein contraction is `ℂ`-linear in the perturbation jet, and the jet of a linear
combination of `C²` fields is the linear combination of the jets. So the set of vacuum perturbations at a point is
closed under finite linear combinations.
-/

open Complex Filter Topology
open scoped ContDiff BigOperators

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower _root_.RHTower.D4BMMetricReconstruction
open CoordinateMetricTwoJet.Linearization

/-- The jet `c K + L`. -/
def jetLin (c : ℂ) (K L : CoordinateMetricTwoJet 4 ℂ) : CoordinateMetricTwoJet 4 ℂ where
  metric := c • K.metric + L.metric
  first k := c • K.first k + L.first k
  second k l := c • K.second k l + L.second k l

section Linear

variable (J K L : CoordinateMetricTwoJet 4 ℂ) (c : ℂ)

theorem inverse_jetLin :
    inverse J (jetLin c K L) = c • inverse J K + inverse J L := by
  simp only [inverse, jetLin, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
    neg_add, smul_neg]

theorem inverseSpatial_jetLin (k : Fin 4) :
    inverseSpatial J (jetLin c K L) k = c • inverseSpatial J K k + inverseSpatial J L k := by
  simp only [inverseSpatial, inverse_jetLin]
  simp only [jetLin, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, neg_add,
    smul_neg, smul_add]
  abel

theorem connection_jetLin (u i j : Fin 4) :
    connection J (jetLin c K L) u i j = c * connection J K u i j + connection J L u i j := by
  simp only [connection, inverse_jetLin]
  rw [mul_left_comm c, ← mul_add]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [jetLin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem connectionSpatial_jetLin (k u i j : Fin 4) :
    connectionSpatial J (jetLin c K L) k u i j =
      c * connectionSpatial J K k u i j + connectionSpatial J L k u i j := by
  simp only [connectionSpatial, inverse_jetLin, inverseSpatial_jetLin]
  rw [mul_left_comm c, ← mul_add]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [jetLin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem curvature_jetLin (u i k l : Fin 4) :
    curvature J (jetLin c K L) u i k l = c * curvature J K u i k l + curvature J L u i k l := by
  simp only [curvature, connectionSpatial_jetLin, connection_jetLin]
  have hS : ∑ m, ((c * connection J K u k m + connection J L u k m) * J.christoffel m l i +
        J.christoffel u k m * (c * connection J K m l i + connection J L m l i) -
      ((c * connection J K u l m + connection J L u l m) * J.christoffel m k i +
        J.christoffel u l m * (c * connection J K m k i + connection J L m k i))) =
      c * ∑ m, (connection J K u k m * J.christoffel m l i + J.christoffel u k m * connection J K m l i -
        (connection J K u l m * J.christoffel m k i + J.christoffel u l m * connection J K m k i)) +
      ∑ m, (connection J L u k m * J.christoffel m l i + J.christoffel u k m * connection J L m l i -
        (connection J L u l m * J.christoffel m k i + J.christoffel u l m * connection J L m k i)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hS]
  ring

theorem ricci_jetLin (i j : Fin 4) :
    ricci J (jetLin c K L) i j = c * ricci J K i j + ricci J L i j := by
  simp only [ricci, curvature_jetLin]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

theorem scalar_jetLin : scalar J (jetLin c K L) = c * scalar J K + scalar J L := by
  simp only [scalar, inverse_jetLin, ricci_jetLin]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem cosmological_jetLin (Λ : ℂ) (i j : Fin 4) :
    cosmological J (jetLin c K L) Λ i j =
      c * cosmological J K Λ i j + cosmological J L Λ i j := by
  simp only [cosmological, einstein, ricci_jetLin, scalar_jetLin]
  simp only [jetLin, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Linear

/-- A perturbation jet is vacuum. -/
def Vac (J K : CoordinateMetricTwoJet 4 ℂ) : Prop := ∀ i j, cosmological J K (-3) i j = 0

theorem Vac.jetLin {J K L : CoordinateMetricTwoJet 4 ℂ} (hK : Vac J K) (hL : Vac J L) (c : ℂ) :
    Vac J (jetLin c K L) := fun i j => by
  rw [cosmological_jetLin, hK i j, hL i j]
  ring

theorem jet_ext {K L : CoordinateMetricTwoJet 4 ℂ} (h0 : K.metric = L.metric) (h1 : K.first = L.first)
    (h2 : K.second = L.second) : K = L := by
  cases K
  cases L
  simp_all

/-- The zero field has a vacuum jet. -/
theorem vac_ofMetricField_zero (J : CoordinateMetricTwoJet 4 ℂ) (p : Fin 4 → ℝ) :
    Vac J (ofMetricField (fun _ => 0) p) := by
  set Z := ofMetricField (fun _ => (0 : Matrix (Fin 4) (Fin 4) ℂ)) p with hZ
  have hz : ∀ i j, ofField (fun _ : Fin 4 → ℝ => (0 : Matrix (Fin 4) (Fin 4) ℂ) i j) p = constant 0 :=
    fun _ _ => ofField_constant 0 p
  have h0 : Z.metric = 0 := by
    ext a b
    change (ofField (fun _ : Fin 4 → ℝ => (0 : Matrix (Fin 4) (Fin 4) ℂ) a b) p).value = 0
    rw [hz]
    rfl
  have h1 : Z.first = 0 := by
    funext k
    ext a b
    change (ofField (fun _ : Fin 4 → ℝ => (0 : Matrix (Fin 4) (Fin 4) ℂ) a b) p).first k = 0
    rw [hz]
    rfl
  have h2 : Z.second = 0 := by
    funext k l
    ext a b
    change (ofField (fun _ : Fin 4 → ℝ => (0 : Matrix (Fin 4) (Fin 4) ℂ) a b) p).second k l = 0
    rw [hz]
    rfl
  have h : Z = jetLin (-1) Z Z := by
    refine jet_ext ?_ ?_ ?_
    · simp [jetLin, h0]
    · funext k
      simp [jetLin, h1]
    · funext k l
      simp [jetLin, h2]
  intro i j
  have hl := cosmological_jetLin J Z Z (-1) (-3) i j
  rw [← h] at hl
  linear_combination hl

/-- The jet of a linear combination of fields. -/
theorem ofMetricField_lin {g₁ g₂ : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} (c : ℂ) {p : Fin 4 → ℝ}
    (h₁ : ∀ a b, ContDiffAt ℝ 2 (fun x => g₁ x a b) p)
    (h₂ : ∀ a b, ContDiffAt ℝ 2 (fun x => g₂ x a b) p) :
    ofMetricField (fun x => c • g₁ x + g₂ x) p =
      jetLin c (ofMetricField g₁ p) (ofMetricField g₂ p) := by
  have he : ∀ a b, ofField (fun x => (c • g₁ x + g₂ x) a b) p =
      ((constant c).mul (ofField (fun x => g₁ x a b) p)).add (ofField (fun x => g₂ x a b) p) := by
    intro a b
    have h3 : (fun x => (c • g₁ x + g₂ x) a b) = fun x => c * g₁ x a b + g₂ x a b := by
      funext x
      simp [Matrix.add_apply, Matrix.smul_apply]
    rw [h3, ofField_add (contDiffAt_const.mul (h₁ a b)) (h₂ a b),
      ofField_mul contDiffAt_const (h₁ a b), ofField_constant]
  refine jet_ext ?_ ?_ ?_
  · ext a b
    change (ofField (fun x => (c • g₁ x + g₂ x) a b) p).value = _
    rw [he]
    simp [ScalarTwoJet.add, ScalarTwoJet.mul, constant, jetLin, ofMetricField]
    rfl
  · funext k
    ext a b
    change (ofField (fun x => (c • g₁ x + g₂ x) a b) p).first k = _
    rw [he]
    simp [ScalarTwoJet.add, ScalarTwoJet.mul, constant, jetLin]
    rfl
  · funext k l
    ext a b
    change (ofField (fun x => (c • g₁ x + g₂ x) a b) p).second k l = _
    rw [he]
    simp [ScalarTwoJet.add, ScalarTwoJet.mul, constant, jetLin]
    rfl

/-- **Vacuum perturbations are closed under finite sums.** -/
theorem vac_sum {ι : Type*} (J : CoordinateMetricTwoJet 4 ℂ) {p : Fin 4 → ℝ} (S : Finset ι) (c : ι → ℂ)
    (g : ι → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hs : ∀ j ∈ S, ∀ a b, ContDiffAt ℝ 2 (fun x => g j x a b) p)
    (hv : ∀ j ∈ S, Vac J (ofMetricField (g j) p)) :
    Vac J (ofMetricField (fun x => ∑ j ∈ S, c j • g j x) p) := by
  classical
  have hsmooth : ∀ T : Finset ι, T ⊆ S → ∀ a b,
      ContDiffAt ℝ 2 (fun x => (∑ j ∈ T, c j • g j x) a b) p := by
    intro T hT a b
    have h1 : (fun x => (∑ j ∈ T, c j • g j x) a b) = fun x => ∑ j ∈ T, c j * g j x a b := by
      funext x
      simp [Matrix.sum_apply, Matrix.smul_apply]
    rw [h1]
    exact ContDiffAt.sum fun j hj => contDiffAt_const.mul (hs j (hT hj) a b)
  have key : ∀ T : Finset ι, T ⊆ S → Vac J (ofMetricField (fun x => ∑ j ∈ T, c j • g j x) p) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simpa using vac_ofMetricField_zero J p
    | insert j T hj ih =>
      intro hT
      have hjS : j ∈ S := hT (Finset.mem_insert_self _ _)
      have hTS : T ⊆ S := fun t ht => hT (Finset.mem_insert_of_mem ht)
      have he : (fun x => ∑ i ∈ insert j T, c i • g i x) =
          fun x => c j • g j x + ∑ i ∈ T, c i • g i x := by
        funext x
        rw [Finset.sum_insert hj]
      rw [he, ofMetricField_lin (c j) (hs j hjS) (hsmooth T hTS)]
      exact (hv j hjS).jetLin (ih hTS) (c j)
  exact key S subset_rfl

/-- The jet of a field depends only on its germ. -/
theorem ofMetricField_congr_germ {f g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ} {x : Fin 4 → ℝ}
    (h : f =ᶠ[𝓝 x] g) : ofMetricField f x = ofMetricField g x := by
  have hE : ∀ a b, (fun y => f y a b) =ᶠ[𝓝 x] fun y => g y a b := fun a b => by
    filter_upwards [h] with y hy
    rw [hy]
  have hf : ∀ a b, ofField (fun y => f y a b) x = ofField (fun y => g y a b) x := by
    intro a b
    have hD : fderiv ℝ (fun y => f y a b) =ᶠ[𝓝 x] fderiv ℝ (fun y => g y a b) := (hE a b).fderiv
    have hd (k : Fin 4) : coordDeriv k (fun y => f y a b) =ᶠ[𝓝 x] coordDeriv k (fun y => g y a b) := by
      filter_upwards [hD] with y hy
      exact congrArg (fun L => L (Pi.single k 1)) hy
    ext i j
    · exact (hE a b).self_of_nhds
    · change fderiv ℝ _ x (Pi.single i 1) = fderiv ℝ _ x (Pi.single i 1)
      rw [(hE a b).fderiv_eq]
    · change fderiv ℝ (coordDeriv j _) x (Pi.single i 1) = fderiv ℝ (coordDeriv j _) x (Pi.single i 1)
      rw [(hd j).fderiv_eq]
  refine jet_ext ?_ ?_ ?_
  · ext a b
    change (ofField (fun y => f y a b) x).value = (ofField (fun y => g y a b) x).value
    rw [hf]
  · funext k
    ext a b
    change (ofField (fun y => f y a b) x).first k = (ofField (fun y => g y a b) x).first k
    rw [hf]
  · funext k l
    ext a b
    change (ofField (fun y => f y a b) x).second k l = (ofField (fun y => g y a b) x).second k l
    rw [hf]

end GaloisForLFunctions.BlackHoleRingdown

end
