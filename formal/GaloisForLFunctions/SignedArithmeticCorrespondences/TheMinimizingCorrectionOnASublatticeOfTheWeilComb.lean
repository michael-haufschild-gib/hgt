import GaloisForLFunctions.SignedArithmeticCorrespondences.WeilMassOnDilatedCombWindows
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheRiemannHypothesisIsExactEventualCombPositivity
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFormOfLogarithmicTailsIsDeterminedByTheRowsOfTheFlatTail

/-!
# Minimizing Weil's form over the sites of a proper sublattice

The coercive inversion in Lauritsen–Lewin–Oldenburg, Lemma 3.2, has a
finite analogue for the arithmetic sublattice. For every exterior
profile there is a unique correction on the sublattice
that annihilates all its rows. The reduction in energy equals the energy of
the correction. The growing sublattice floor controls the inverse response
to any forcing on the rows.
-/

open Filter Finset
noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart

/-- Zero extension from a finite set of sites. -/
def combSiteExtension (E : Finset ℕ) (x : E → ℝ) (n : ℕ) : ℝ :=
  if h : n ∈ E then x ⟨n,h⟩ else 0

/-- The row of the full form tested at a single site. -/
def combSiteRow (S : Finset ℕ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  formBilin S c (fun n => if n=i then 1 else 0)

private theorem site_expansion (E : Finset ℕ) (x : E → ℝ) :
    combSiteExtension E x = fun n => ∑ i : E, x i * (if n=(i:ℕ) then 1 else 0) := by
  classical
  funext n
  by_cases h : n ∈ E
  · have he (i : E) : n = (i:ℕ) ↔ (⟨n,h⟩ : E) = i := Subtype.ext_iff.symm
    simp only [combSiteExtension, dif_pos h, he, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ, if_true]
  · have he (i : E) : n ≠ (i:ℕ) := fun eq => h (eq ▸ i.property)
    simp [combSiteExtension,h,he]

private theorem test_sites (S E : Finset ℕ) (c : ℕ → ℝ) (x : E → ℝ) :
    formBilin S c (combSiteExtension E x) = ∑ i : E, x i * combSiteRow S c i := by
  rw [site_expansion, formBilin_sum_right]
  exact sum_congr rfl fun i _ => formBilin_const_mul_right S (x i) c _

private theorem extension_add (E : Finset ℕ) (x y : E → ℝ) :
    combSiteExtension E (x+y) = fun n => combSiteExtension E x n + combSiteExtension E y n := by
  funext n
  by_cases h : n ∈ E <;> simp [combSiteExtension,h]

private def siteOperator (S E : Finset ℕ) : (E → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun x i := combSiteRow S (combSiteExtension E x) i
  map_add' x y := by
    funext i
    exact (congrArg (fun f => combSiteRow S f i) (extension_add E x y)).trans
      (formBilin_add_left S _ _ _)
  map_smul' t x := by
    funext i
    have he : combSiteExtension E (t • x) = fun n => t * combSiteExtension E x n := by
      funext n
      by_cases h : n ∈ E <;> simp [combSiteExtension,h]
    rw [he]
    exact formBilin_const_mul_left S t _ _

private theorem site_energy (S E : Finset ℕ) (x : E → ℝ) :
    combForm S (combSiteExtension E x) = ∑ i : E, x i * siteOperator S E x i := by
  rw [← formBilin_self, test_sites]
  rfl

/-- The restricted Weil matrix solves every prescribed force on the
sublattice. The squared gain is bounded by the inverse squared mass floor. -/
theorem eventually_comb_site_response (d : ℕ+) (hd : 2 ≤ (d:ℕ)) (Q : ℕ+) (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      let S := Ioc ((d:ℕ)*N) ((d:ℕ)*(N+(Q:ℕ)*N))
      let E := S.filter (fun n => (d:ℕ) ∣ n)
      ∀ f : E → ℝ, ∃! x : E → ℝ, (∀ i : E, combSiteRow S (combSiteExtension E x) i = f i) ∧
        B^2*(∑ i : E, (x i)^2) ≤ ∑ i : E, (f i)^2 := by
  filter_upwards [eventually_full_comb_on_multiples d hd Q B] with N hfloor
  intro S E
  let L := siteOperator S E
  have coercive (x : E → ℝ) : B*(∑ i : E, (x i)^2) ≤ ∑ i : E, x i * L x i := by
    rw [← site_energy]
    have z (n : ℕ) (_ : n ∈ S) (hn : ¬ (d:ℕ) ∣ n) : combSiteExtension E x n=0 := by
      exact dif_neg (fun h => hn (mem_filter.mp h).2)
    have hs : (∑ n ∈ E, (combSiteExtension E x n)^2) = ∑ n ∈ S, (combSiteExtension E x n)^2 :=
      sum_subset (filter_subset ..) (fun n _ hn => by simp [combSiteExtension,hn])
    have hx : (∑ i : E, (x i)^2) = ∑ n ∈ E, (combSiteExtension E x n)^2 := by
      rw [← sum_attach]
      exact sum_congr rfl fun i _ => by simp [combSiteExtension,i.property]
    rw [hx,hs]
    exact hfloor _ z
  have inj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have h := coercive x
    rw [hx] at h
    simp only [Pi.zero_apply, mul_zero, sum_const_zero] at h
    have hz : (∑ i : E, (x i)^2) ≤ 0 := nonpos_of_mul_nonpos_right h hB
    funext i
    have hle := (single_le_sum (f:=fun j : E => (x j)^2) (fun j _ => sq_nonneg _) (mem_univ i)).trans hz
    exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  intro f
  obtain ⟨x,hx⟩ := LinearMap.surjective_of_injective inj f
  refine ⟨x,⟨fun i => congrFun hx i,?_⟩,fun y hy => inj ((funext hy.1).trans hx.symm)⟩
  let X := ∑ i : E, (x i)^2
  let F := ∑ i : E, (f i)^2
  change B^2*X ≤ F
  have h := coercive x
  rw [hx] at h
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  rcases hX.eq_or_lt with hz | hp
  · rw [← hz,mul_zero]
    exact sum_nonneg fun _ _ => sq_nonneg _
  · have hsq := (sq_le_sq' (by linarith only [h,mul_nonneg hB.le hX]) h).trans
        (sum_mul_sq_le_sq_mul_sq univ x f)
    exact le_of_mul_le_mul_right (a:=X) (by
      dsimp only [X,F] at *
      nlinarith only [hsq]) hp

/-- At every sufficiently large scale, each exterior profile has a correction
whose residual is orthogonal to all sublattice sites. The energy released by
the correction is its own Weil energy. Every perturbation restores exactly
its own energy, with the prescribed mass floor. -/
theorem eventually_comb_minimizing_correction (d : ℕ+) (hd : 2 ≤ (d:ℕ)) (Q : ℕ+)
    (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      let S := Ioc ((d:ℕ)*N) ((d:ℕ)*(N+(Q:ℕ)*N))
      let E := S.filter (fun n => (d:ℕ) ∣ n)
      ∀ o : ℕ → ℝ, ∃ x : E → ℝ,
        let c := fun n => o n + combSiteExtension E x n
        (∀ i : E, combSiteRow S c i = 0) ∧
        combForm S c = combForm S o - combForm S (combSiteExtension E x) ∧
        (∀ y : E → ℝ, combForm S (fun n => c n + combSiteExtension E y n) =
          combForm S c + combForm S (combSiteExtension E y)) ∧
        (∀ y : E → ℝ, B*(∑ n ∈ S, (combSiteExtension E y n)^2) ≤
          combForm S (fun n => c n + combSiteExtension E y n) - combForm S c) := by
  filter_upwards [eventually_comb_site_response d hd Q B hB,
    eventually_full_comb_on_multiples d hd Q B] with N respond floor
  intro S E o
  obtain ⟨x,hx,_⟩ := respond (fun i => -combSiteRow S o i)
  refine ⟨x,?_⟩
  intro c
  have row (i : E) : combSiteRow S c i = 0 := by
    have hi := hx.1 i
    change combSiteRow S (combSiteExtension E x) i = -combSiteRow S o i at hi
    change formBilin S (fun n => o n + combSiteExtension E x n) _ = 0
    rw [formBilin_add_left]
    change combSiteRow S o i + combSiteRow S (combSiteExtension E x) i = 0
    rw [hi,add_neg_cancel]
  have orth (y : E → ℝ) : formBilin S c (combSiteExtension E y) = 0 := by
    rw [test_sites]
    exact sum_eq_zero fun i _ => by rw [row,mul_zero]
  have release : combForm S c = combForm S o - combForm S (combSiteExtension E x) := by
    have h := orth x
    change formBilin S (fun n => o n + combSiteExtension E x n) _ = 0 at h
    rw [formBilin_add_left, formBilin_self] at h
    change combForm S (fun n => o n + combSiteExtension E x n) = _
    rw [AbsoluteGeometryOfSpecZ.combForm_add]
    linarith only [h]
  have exact_cost (y : E → ℝ) : combForm S (fun n => c n + combSiteExtension E y n) =
      combForm S c + combForm S (combSiteExtension E y) := by
    rw [AbsoluteGeometryOfSpecZ.combForm_add,orth,mul_zero,add_zero]
  refine ⟨row,release,exact_cost,fun y => ?_⟩
  rw [exact_cost,add_sub_cancel_left]
  exact floor _ (fun n _ hn => dif_neg fun h => hn (mem_filter.mp h).2)

/-- The full eventual Weil sign is equivalent to testing, on cofinal aligned
windows, just the profiles whose exact Weil rows at every even site vanish.
Their odd values are free; their even values are determined by minimization. -/
theorem rh_iff_cofinal_even_row_equilibria :
    RiemannHypothesis ↔ ∀ K : ℕ, 1 ≤ K → ∃ᶠ N : ℕ in atTop,
      let S := Ioc (2*N) (2*(N+3*K*N))
      ∀ c : ℕ → ℝ, (∀ i ∈ S, 2 ∣ i → combSiteRow S c i = 0) → 0 ≤ combForm S c := by
  let S (K N : ℕ) := Ioc (2*N) (2*(N+3*K*N))
  have win (K N : ℕ) : S K N = Ioc (2*N) (2*N+3*K*(2*N)) := by
    dsimp only [S]; congr 1; ring
  have top : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by decide : 0 < 2)) tendsto_id
  constructor
  · intro h K _
    apply Eventually.frequently
    filter_upwards [top (eventually_combForm_nonneg_of_riemannHypothesis h K)] with N hN
    intro c _
    change 0 ≤ combForm (S K N) c
    rw [win]
    exact hN c
  · intro h
    apply riemannHypothesis_of_frequently_combForm_ge
    intro K hk η hη
    let Q : ℕ+ := ⟨3*K,by omega⟩
    have minimize := eventually_comb_minimizing_correction (2:ℕ+) (by decide) Q 1 zero_lt_one
    have floor := eventually_full_comb_on_multiples (2:ℕ+) (by decide) Q 1
    apply frequently_atTop.mpr
    intro M
    obtain ⟨N,⟨⟨hN,hmin⟩,hfloor⟩,hM⟩ := ((((h K hk).and_eventually minimize).and_eventually floor).and_eventually
      (eventually_ge_atTop M)).exists
    refine ⟨2*N,by omega,fun o => ?_⟩
    rw [←win]
    apply (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη.le) (sum_nonneg fun _ _ => sq_nonneg _)).trans
    let E := (S K N).filter (fun n => 2 ∣ n)
    obtain ⟨x,hrow,hrelease,_,_⟩ := hmin o
    let e := combSiteExtension E x
    have hc : 0 ≤ combForm (S K N) (fun n => o n+e n) :=
      hN _ (fun i hi hd => hrow ⟨i,mem_filter.mpr ⟨hi,hd⟩⟩)
    have he := hfloor e (fun n _ hn => dif_neg (fun h => hn (mem_filter.mp h).2))
    change 1*(∑ n ∈ S K N, (e n)^2) ≤ combForm (S K N) e at he
    change combForm (S K N) (fun n => o n+e n) = combForm (S K N) o-combForm (S K N) e at hrelease
    linarith only [hc,hrelease,he,sum_nonneg (s:=S K N) (fun n _ => sq_nonneg (e n))]

#print axioms rh_iff_cofinal_even_row_equilibria
#print axioms eventually_comb_site_response
#print axioms eventually_comb_minimizing_correction
end GaloisForLFunctions.SignedArithmeticCorrespondences
