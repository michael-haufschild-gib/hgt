import GaloisForLFunctions.HTGeometry.DispersivePDE.TheGeometricMeanThresholdForFourUnequalModes

/-!
# Response of four synchronized modes to a change of coupling

The energy is affine in the coupling at a fixed amplitude. Comparing
the two global minima at different couplings and paying their sharp
radial stability costs bounds the energy secant from both sides.
It also forces each individual positive amplitude to increase.
-/

noncomputable section
namespace HTGeometry.CriticalQuartet

/-- Positive couplings below the geometric-mean threshold. -/
abbrev SubcriticalCoupling (μ : Fin 4 → ℝ) := {b : ℝ // 0<b ∧ b^4<product μ}

/-- The unique positive synchronized state at a subcritical coupling. -/
def groundAmplitude {μ : Fin 4 → ℝ} {m : ℝ} (hμ : ∀ i, 0<μ i) (hm : 0<m)
    (b : SubcriticalCoupling μ) : Fin 4 → ℝ :=
  ((unique_positive_iff hμ hm b.2.1).mpr b.2.2).exists.choose

theorem groundAmplitude_synchronized {μ : Fin 4 → ℝ} {m : ℝ} (hμ : ∀ i, 0<μ i) (hm : 0<m)
    (b : SubcriticalCoupling μ) : Synchronized μ m b (groundAmplitude hμ hm b) :=
  ((unique_positive_iff hμ hm b.2.1).mpr b.2.2).exists.choose_spec

/-- The squared change in amplitudes costs at least m on each side of
the secant between the two minimum energies. -/
theorem coupling_energy_sandwich {μ x y : Fin 4 → ℝ} {m b c : ℝ}
    (hm : 0<m) (hb : 0<b) (hc : 0<c) (hx : Synchronized μ m b x) (hy : Synchronized μ m c y) :
    let D := total (fun i => (y i-x i)^2)
    let G := energy μ m b x-energy μ m c y
    4*(c-b)*product x+m*D ≤ G ∧ G ≤ 4*(c-b)*product y-m*D := by
  intro D G
  have ay (i : Fin 4) : |y i|=y i := abs_of_pos (hy.1 i)
  have ax (i : Fin 4) : |x i|=x i := abs_of_pos (hx.1 i)
  have p := (best_radial_stability hm hb hx m).mpr le_rfl y
  have q := (best_radial_stability hm hc hy m).mpr le_rfl x
  simp only [ay] at p
  simp only [ax] at q
  have swap : (fun i => (x i-y i)^2)=(fun i => (y i-x i)^2) := funext fun _ => by ring
  rw [swap] at q
  change m*D≤_ at p q
  have shift (z : Fin 4 → ℝ) : energy μ m c z=energy μ m b z-4*(c-b)*product z := by
    unfold energy
    ring
  dsimp only [G]
  constructor <;> linarith only [p,q,shift x,shift y]

private theorem different_ground_states {μ x y : Fin 4 → ℝ} {m b c : ℝ} (hbc : b<c)
    (hx : Synchronized μ m b x) (hy : Synchronized μ m c y) : x≠y := by
  rintro rfl
  have strict := mul_lt_mul_of_pos_right hbc (product_pos hx.1)
  linarith only [hx.2 0,hy.2 0,strict]

/-- Each minimum-energy secant strictly separates the two endpoint
products. This gives strict concavity of the minimum energy. -/
theorem coupling_release_secant {μ x y : Fin 4 → ℝ} {m b c : ℝ}
    (hm : 0<m) (hb : 0<b) (hbc : b<c) (hx : Synchronized μ m b x) (hy : Synchronized μ m c y) :
    let slope := (energy μ m b x-energy μ m c y)/(c-b)
    4*product x<slope ∧ slope<4*product y := by
  intro slope
  obtain ⟨j,hj⟩ : ∃ i, y i≠x i := by
    by_contra! h
    exact different_ground_states hbc hx hy (funext h).symm
  have dpos : 0<total (fun i => (y i-x i)^2) :=
    (sq_pos_of_ne_zero (sub_ne_zero.mpr hj)).trans_le (le_total (fun i => sq_nonneg (y i-x i)) j)
  obtain ⟨lower,upper⟩ := coupling_energy_sandwich hm hb (hb.trans hbc) hx hy
  exact ⟨(lt_div_iff₀ (sub_pos.mpr hbc)).mpr (by linarith only [lower,mul_pos hm dpos]),
    (div_lt_iff₀ (sub_pos.mpr hbc)).mpr (by linarith only [upper,mul_pos hm dpos])⟩

/-- Along the entire positive subcritical branch, increasing the coupling
strictly increases every amplitude, even with unequal self-interactions. -/
theorem groundAmplitude_strictMono {μ : Fin 4 → ℝ} {m : ℝ} (hμ : ∀ i, 0<μ i) (hm : 0<m)
    (i : Fin 4) : StrictMono (fun b : SubcriticalCoupling μ => groundAmplitude hμ hm b i) := by
  intro b c hbc
  let x := groundAmplitude hμ hm b
  let y := groundAmplitude hμ hm c
  have hx := groundAmplitude_synchronized hμ hm b
  have hy := groundAmplitude_synchronized hμ hm c
  change Synchronized μ m b x at hx
  change Synchronized μ m c y at hy
  change x i<y i
  have h : (b:ℝ)<c := hbc
  obtain ⟨lo,hi⟩ := coupling_release_secant hm b.2.1 h hx hy
  have prod : product x<product y := by linarith only [lo.trans hi]
  have load : (b:ℝ)*product x < (c:ℝ)*product y :=
    (mul_lt_mul_of_pos_right h (product_pos hx.1)).trans (mul_lt_mul_of_pos_left prod c.2.1)
  have positive : 0<μ i*x i^2-m := by
    by_contra! he
    have bad := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x i)) he
    linarith only [hx.2 i,bad,mul_pos b.2.1 (product_pos hx.1)]
  have factor : 0≤μ i*(y i^2+x i^2)-m := by
    linarith only [positive,mul_nonneg (hμ i).le (sq_nonneg (y i))]
  by_contra! rev
  have bad := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (pow_le_pow_left₀ (hy.1 i).le rev 2)) factor
  linarith only [bad,hx.2 i,hy.2 i,load]

/-- Any two consecutive secants of the minimum energy have strictly
decreasing slopes. -/
theorem ground_energy_secants_decrease {μ : Fin 4 → ℝ} {m : ℝ} (hμ : ∀ i, 0<μ i) (hm : 0<m)
    {b c d : SubcriticalCoupling μ} (hbc : b<c) (hcd : c<d) :
    let V := fun r : SubcriticalCoupling μ => energy μ m r (groundAmplitude hμ hm r)
    (V d-V c)/((d:ℝ)-c)<(V c-V b)/((c:ℝ)-b) := by
  intro V
  have low := (coupling_release_secant hm c.2.1 (show (c:ℝ)<d from hcd)
    (groundAmplitude_synchronized hμ hm c) (groundAmplitude_synchronized hμ hm d)).1
  have high := (coupling_release_secant hm b.2.1 (show (b:ℝ)<c from hbc)
    (groundAmplitude_synchronized hμ hm b) (groundAmplitude_synchronized hμ hm c)).2
  have cross := high.trans low
  change (V b-V c)/_<(V c-V d)/_ at cross
  simpa only [←neg_div,neg_sub] using neg_lt_neg cross

#print axioms coupling_energy_sandwich
#print axioms coupling_release_secant
#print axioms groundAmplitude_strictMono
#print axioms ground_energy_secants_decrease
end HTGeometry.CriticalQuartet
