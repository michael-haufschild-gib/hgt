import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Configurations

/-! # Single-draw probabilities and the collision scale in physical prime packets -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Filter Topology Real Set _root_.RHTower
open BinaryOrientation.LargestPrime.Bands

variable {S : Finset Nat.Primes}

def serial (p : ↥S) : ℕ := p.val.val

theorem serial_inj (S : Finset Nat.Primes) : Function.Injective (serial (S := S)) :=
  fun _ _ he => Subtype.ext (Subtype.ext he)

def modes (S : Finset Nat.Primes) (P : Finset ℕ) := Finset.univ.filter fun p : ↥S => serial p ∈ P

theorem modes_mono {P Q : Finset ℕ} (h : P ⊆ Q) : modes S P ⊆ modes S Q :=
  fun _ hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h (Finset.mem_filter.mp hp).2⟩

theorem sub_image {P Q : Finset ℕ} (hP : (modes S P).image serial = P) (hQ : Q ⊆ P) :
    (modes S Q).image serial = Q := by
  ext n
  constructor
  · intro hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp hp).2
  · intro hn
    obtain ⟨p,_,he⟩ := Finset.mem_image.mp (hP.symm ▸ hQ hn)
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hn⟩,he⟩

/-- All natural prime labels in the two endpoint packets occur in the physical moving cutoff. -/
theorem mode_coverage {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) :
    ∀ᶠ h in criticalApproach, let P := both D k (c/h.val)
      (modes (added c d h) P).image serial = P := by
  filter_upwards [physical_window hc hcd hD hk] with h hw
  ext n
  constructor
  · intro hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact (Finset.mem_filter.mp hp).2
  · intro hn
    obtain ⟨R,_,he⟩ := Finset.mem_image.mp (hw.1.symm ▸ hn)
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp R.property
    have hr : R = oneMode p := Subtype.ext hp
    rw [hr,label_oneMode] at he
    change serial p = n at he
    exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hn⟩,he⟩

def draw (S : Finset Nat.Primes) (P : Finset ℕ) (b t : ℝ) (p : ↥S) :=
  if p ∈ modes S P then shifted b t (serial p)/mass (shifted b t) P else 0

theorem draw_nonneg (P : Finset ℕ) (b t : ℝ) (p : ↥S) : 0 ≤ draw S P b t p := by
  unfold draw
  split
  · exact div_nonneg (shifted_pos _ _ _).le (Finset.sum_nonneg fun _ _ => (shifted_pos _ _ _).le)
  · exact le_rfl

theorem draw_total {P : Finset ℕ} (hp : P.Nonempty) (him : (modes S P).image serial = P) (b t : ℝ) :
    ∑ p, draw S P b t p = 1 := by
  classical
  have he : (∑ p ∈ modes S P, shifted b t (serial p)) = mass (shifted b t) P := by
    conv_rhs => rw [mass,← him,Finset.sum_image (serial_inj S).injOn]
  simp only [draw,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,← Finset.sum_div,
    he,div_self (mass_pos (shifted_pos b t) hp).ne']

theorem draw_event {P Q : Finset ℕ} (him : (modes S P).image serial = P) (hQ : Q ⊆ P) (b t : ℝ) :
    (∑ p ∈ modes S Q, draw S P b t p) = share (shifted b t) P Q := by
  change (∑ p ∈ modes S Q, if p ∈ modes S P then _ else 0) = _
  rw [Finset.sum_congr rfl (fun p hp => if_pos (modes_mono hQ hp)),← Finset.sum_div]
  unfold share
  congr 1
  conv_rhs => rw [mass,← sub_image him hQ,Finset.sum_image (serial_inj S).injOn]

theorem squared_draw {P : Finset ℕ} (him : (modes S P).image serial = P) (b t : ℝ) :
    (∑ p, draw S P b t p^2) = mass (shifted (2*b) t) P/(mass (shifted b t) P)^2 := by
  have sqw (p : ℕ) : shifted b t p^2 = shifted (2*b) t p := by
    rw [shifted,shifted,sq,← exp_add]; congr 1; ring
  have eqw p : draw S P b t p^2 = if p ∈ modes S P then shifted (2*b) t (serial p)/(mass (shifted b t) P)^2 else 0 := by
    by_cases hp : p ∈ modes S P <;> simp only [draw,hp,if_true,if_false,div_pow,sqw,zero_pow (Nat.succ_ne_zero 1)]
  rw [Finset.sum_congr rfl (fun p _ => eqw p),← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,← Finset.sum_div]
  congr 1
  conv_rhs => rw [mass,← him,Finset.sum_image (serial_inj S).injOn]

def collisionScale (D k b : ℝ) := (1+odds D k (2*b))/(1+odds D k b)^2

theorem scale_zero : Tendsto scale atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => t^2/exp t) atTop (𝓝 0)
  simpa only [div_eq_mul_inv,exp_neg] using tendsto_pow_mul_exp_neg_atTop_nhds_zero 2

/-- Exact leading scale of the probability that two independent physical draws coincide. -/
theorem squared_draw_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    Tendsto (fun h => let t := c/h.val
      (∑ p, draw (added c d h) (both D k t) b t p^2)/scale t) criticalApproach (𝓝 (collisionScale D k b)) := by
  have hd := add_pos zero_lt_one (odds_pos D hk b)
  have H := (both_mass hD hk (2*b)).div ((both_mass hD hk b).pow 2) (pow_ne_zero _ hd.ne')
  apply (H.comp (translation_limit hc)).congr'
  filter_upwards [mode_coverage hc hcd hD hk] with h hw
  dsimp only
  rw [squared_draw hw]
  change scale _ * _ / (scale _ * _)^2 = _ / _^2 / scale _
  rw [mul_pow]
  by_cases hz : mass (shifted b (c/h.val)) (both D k (c/h.val)) = 0
  · rw [hz,zero_pow (Nat.succ_ne_zero 1),mul_zero,div_zero,div_zero,zero_div]
  · have hs : scale (c/h.val) ≠ 0 := (div_pos (sq_pos_of_pos (div_pos hc h.property)) (exp_pos _)).ne'
    field_simp [hs,hz]

#print axioms mode_coverage
#print axioms squared_draw_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
