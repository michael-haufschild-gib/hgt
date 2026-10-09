import GaloisForLFunctions.HTGeometry.MonotoneQuantileTransport

/-!
# Quantile rearrangement of pair and jump energies

Let `g ≥ 0` be bounded, measurable and supported on a measurable set `S` of finite measure `L`.
Its quantile transport `g*` (`QuantileTransport.transport`) is `g ∘ G` on `(0, L)` and zero
elsewhere, where `G` is the quantile function of `S` (made measurable).

* `g*` has the same square integral as `g` (`integral_sq_transport`).
* For every nonnegative kernel `κ` decreasing on `(0, ∞)` with `min(κ, n)` integrable there, the
  jump energy `∫_{x>0} κ(x) ∫ (h(u) − h(u+x))² du dx` does not increase
  (`lintegral_jump_transport_le`).
* For every nonnegative kernel `κ` increasing on `[0, ∞)`, the pair energy
  `∫∫ h(u) h(v) κ(|u − v|)` does not increase (`lintegral_pair_transport_le`).

The jump energy is `2‖h‖² ∫ κ − ∫∫ h(u) h(v) κ(|u − v|)` after truncation, so both statements
reduce to the cross-term inequalities of `MonotoneQuantileTransport`, followed by monotone
convergence in the truncation level.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace QuantileTransport

/-! ### Bounded functions supported on a set of finite measure -/

/-- `h` is measurable, bounded by `C` and supported on the measurable set `A` of finite measure. -/
structure BddSupp (A : Set ℝ) (h : ℝ → ℝ) (C : ℝ) : Prop where
  meas : Measurable h
  bound : ∀ x, |h x| ≤ C
  supp : ∀ x ∉ A, h x = 0
  setm : MeasurableSet A
  fin : volume A ≠ ⊤

namespace BddSupp

variable {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ}

theorem integrable (hh : BddSupp A h C) : Integrable h := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hh.supp
  exact Measure.integrableOn_of_bounded hh.fin hh.meas.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hh.bound x)

theorem integrable_sq (hh : BddSupp A h C) : Integrable fun x => h x ^ 2 := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := A) ?_
    (fun x (hx : x ∉ A) => by simp [hh.supp x hx])
  refine Measure.integrableOn_of_bounded (M := C ^ 2) hh.fin (hh.meas.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hh.bound x) 2

theorem integrable_mul_shift (hh : BddSupp A h C) (x : ℝ) :
    Integrable fun u => h u * h (u + x) := by
  have := hh.integrable.bdd_mul (c := C) (f := fun u => h (u + x))
    (hh.meas.comp (measurable_id.add_const x)).aestronglyMeasurable
    (ae_of_all _ fun u => by rw [Real.norm_eq_abs]; exact hh.bound _)
  simpa [mul_comm] using this

end BddSupp

/-- The autocorrelation `c_h(x) = ∫ h(u) h(u + x) du`. -/
def autocorr (h : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, h u * h (u + x)

theorem autocorr_neg (h : ℝ → ℝ) (x : ℝ) : autocorr h (-x) = autocorr h x := by
  unfold autocorr
  rw [← integral_add_right_eq_self (fun u => h u * h (u + -x)) x]
  congr 1
  funext u
  rw [show u + x + -x = u by ring, mul_comm]

/-- **Jump energy in autocorrelation form**: `∫ (h(u) − h(u+x))² = 2‖h‖² − 2c_h(x)`. -/
theorem integral_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (hh : BddSupp A h C) (x : ℝ) :
    ∫ u, (h u - h (u + x)) ^ 2 = 2 * (∫ u, h u ^ 2) - 2 * autocorr h x := by
  have h1 := hh.integrable_sq
  have h2 : Integrable fun u => h (u + x) ^ 2 := h1.comp_add_right x
  have h3 := hh.integrable_mul_shift x
  have e : (fun u => (h u - h (u + x)) ^ 2) =
      fun u => h u ^ 2 + h (u + x) ^ 2 - 2 * (h u * h (u + x)) := by
    funext u; ring
  have h12 : Integrable fun u => h u ^ 2 + h (u + x) ^ 2 := h1.add h2
  rw [e, integral_sub h12 (h3.const_mul 2)]
  rw [show (∫ u, (h u ^ 2 + h (u + x) ^ 2)) = (∫ u, h u ^ 2) + ∫ u, h (u + x) ^ 2 from
    integral_add h1 h2, integral_const_mul, integral_add_right_eq_self (fun u => h u ^ 2) x, autocorr]
  ring

section PairIdentity

variable {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} {k : ℝ → ℝ} {K : ℝ}

/-- The shifted pair integrand `(u, x) ↦ h(u) h(x + u) k(|x|)` is integrable on the plane. -/
theorem integrable_shiftPair (hh : BddSupp A h C) (hk : Measurable k) (hkK : ∀ r, |k r| ≤ K) :
    Integrable (Function.uncurry fun u x => h u * h (x + u) * k |x|) (volume.prod volume) := by
  have hmeas : Measurable (Function.uncurry fun u x : ℝ => h u * h (x + u) * k |x|) :=
    ((hh.meas.comp measurable_fst).mul (hh.meas.comp (measurable_snd.add measurable_fst))).mul
      (hk.comp measurable_snd.abs)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hkK 0)
  have hinner : ∀ u, ∫ x, ‖Function.uncurry (fun u x : ℝ => h u * h (x + u) * k |x|) (u, x)‖ ≤
      |h u| * K * ∫ x, |h x| := by
    intro u
    have hi : Integrable fun x => |h u| * K * |h (x + u)| :=
      (hh.integrable.abs.comp_add_right u).const_mul _
    calc ∫ x, ‖Function.uncurry (fun u x : ℝ => h u * h (x + u) * k |x|) (u, x)‖
        ≤ ∫ x, |h u| * K * |h (x + u)| := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hi
            (ae_of_all _ fun x => ?_)
          simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hkK _) (abs_nonneg _))
            (abs_nonneg _)
      _ = |h u| * K * ∫ x, |h x| := by
          rw [integral_const_mul, integral_add_right_eq_self (fun x => |h x|) u]
  refine ⟨ae_of_all _ fun u => ?_, ?_⟩
  · refine ((hh.integrable.comp_add_right u).bdd_mul (c := |h u| * K)
      (f := fun x => h u * k |x|) ((measurable_const.mul (hk.comp measurable_id.abs)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)).congr (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hkK _) (abs_nonneg _)
    · simp only [Function.uncurry_apply_pair]; ring
  · refine (hh.integrable.abs.mul_const (K * ∫ x, |h x|)).mono'
      (hmeas.norm.aestronglyMeasurable.integral_prod_right') (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc _ ≤ |h u| * K * ∫ x, |h x| := hinner u
      _ = |h u| * (K * ∫ x, |h x|) := by ring

/-- **Pair identity**: `∫∫ h(u) h(v) k(|u − v|) = ∫ k(|x|) c_h(x) dx`. -/
theorem integral_pair_eq_autocorr (hh : BddSupp A h C) (hk : Measurable k) (hkK : ∀ r, |k r| ≤ K) :
    ∫ p : ℝ × ℝ, h p.1 * h p.2 * k |p.1 - p.2| = ∫ x, k |x| * autocorr h x := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hkK 0)
  have hint : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * k |p.1 - p.2|) (volume.prod volume) := by
    refine ((hh.integrable.abs.mul_prod hh.integrable.abs).mul_const K).mono'
      (((hh.meas.comp measurable_fst).mul (hh.meas.comp measurable_snd)).mul
        (hk.comp (measurable_fst.sub measurable_snd).abs)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hkK _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  have hin : ∀ u : ℝ, ∫ v, h u * h v * k |u - v| = ∫ x, h u * h (x + u) * k |x| := by
    intro u
    rw [← integral_add_right_eq_self (fun v => h u * h v * k |u - v|) u]
    congr 1
    funext x
    rw [show u - (x + u) = -x by ring, abs_neg]
  simp_rw [hin]
  rw [integral_integral_swap (integrable_shiftPair hh hk hkK)]
  congr 1
  funext x
  unfold autocorr
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [add_comm x u]
  ring

theorem integrable_kernel_mul_autocorr (hh : BddSupp A h C) (hk : Measurable k)
    (hkK : ∀ r, |k r| ≤ K) : Integrable fun x => k |x| * autocorr h x := by
  have := (integrable_shiftPair hh hk hkK).integral_prod_right
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [Function.uncurry_apply_pair]
  unfold autocorr
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [add_comm x u]
  ring

/-- **Symmetric split**: `∫ k(|x|) c_h(x) dx = 2 ∫_{x>0} k(x) c_h(x) dx`. -/
theorem integral_pair_eq_two_mul_Ioi (hh : BddSupp A h C) (hk : Measurable k)
    (hkK : ∀ r, |k r| ≤ K) :
    ∫ p : ℝ × ℝ, h p.1 * h p.2 * k |p.1 - p.2| = 2 * ∫ x in Ioi 0, k x * autocorr h x := by
  rw [integral_pair_eq_autocorr hh hk hkK]
  have hI := integrable_kernel_mul_autocorr hh hk hkK
  rw [← intervalIntegral.integral_Iio_add_Ici hI.integrableOn hI.integrableOn,
    integral_Ici_eq_integral_Ioi, ← integral_Iic_eq_integral_Iio,
    ← integral_comp_neg_Ioi 0 (fun x => k |x| * autocorr h x), neg_zero]
  have e1 : ∫ x in Ioi (0 : ℝ), k |-x| * autocorr h (-x) = ∫ x in Ioi (0 : ℝ), k x * autocorr h x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      rw [abs_neg, autocorr_neg, abs_of_pos hx]
  have e2 : ∫ x in Ioi (0 : ℝ), k |x| * autocorr h x = ∫ x in Ioi (0 : ℝ), k x * autocorr h x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
  rw [e1, e2]
  ring

end PairIdentity

/-! ### The transported function -/

section Transport

variable {S : Set ℝ} {g : ℝ → ℝ} {C : ℝ}

/-- A pair integral of a function vanishing off `A` lives on `A × A`. -/
theorem integral_pair_eq_restrict {A : Set ℝ} {h : ℝ → ℝ} (hA0 : ∀ x ∉ A, h x = 0) (k : ℝ → ℝ) :
    ∫ p : ℝ × ℝ, h p.1 * h p.2 * k |p.1 - p.2| =
      ∫ p, h p.1 * h p.2 * k |p.1 - p.2| ∂((volume.restrict A).prod (volume.restrict A)) := by
  rw [Measure.prod_restrict, setIntegral_eq_integral_of_forall_compl_eq_zero, Measure.volume_eq_prod]
  intro p hp
  rcases not_and_or.mp (show ¬(p.1 ∈ A ∧ p.2 ∈ A) from hp) with h1 | h2
  · rw [hA0 _ h1]; ring
  · rw [hA0 _ h2]; ring

/-- The measurable version of the quantile function. -/
def quantileMk (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) : ℝ → ℝ :=
  (aemeasurable_quantile hSm hS).mk (quantile S)

/-- **The quantile transport** `g* = 1_{(0,L)} · g ∘ G`. -/
def transport (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) (g : ℝ → ℝ) : ℝ → ℝ :=
  (Ioo 0 (volume S).toReal).indicator fun x => g (quantileMk hSm hS x)

theorem transport_nonneg (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) (hg0 : ∀ x, 0 ≤ g x)
    (x : ℝ) : 0 ≤ transport hSm hS g x :=
  Set.indicator_nonneg (fun _ _ => hg0 _) x

theorem transport_bddSupp (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) (hg : BddSupp S g C) :
    BddSupp (Ioo 0 (volume S).toReal) (transport hSm hS g) C where
  meas := (hg.meas.comp (aemeasurable_quantile hSm hS).measurable_mk).indicator measurableSet_Ioo
  bound x := by
    unfold transport
    by_cases hx : x ∈ Ioo 0 (volume S).toReal
    · rw [Set.indicator_of_mem hx]; exact hg.bound _
    · rw [Set.indicator_of_notMem hx, abs_zero]; exact (abs_nonneg _).trans (hg.bound 0)
  supp x hx := Set.indicator_of_notMem hx _
  setm := measurableSet_Ioo
  fin := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top

/-- **Transport preserves the `L²` norm.** -/
theorem integral_sq_transport (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) (hg : BddSupp S g C) :
    ∫ x, transport hSm hS g x ^ 2 = ∫ x, g x ^ 2 := by
  have e : (fun x => transport hSm hS g x ^ 2) =
      (Ioo 0 (volume S).toReal).indicator fun x => g (quantileMk hSm hS x) ^ 2 := by
    funext x
    unfold transport
    by_cases hx : x ∈ Ioo 0 (volume S).toReal
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
  rw [e, integral_indicator measurableSet_Ioo]
  have hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 (volume S).toReal)),
      g (quantileMk hSm hS x) ^ 2 = g (quantile S x) ^ 2 := by
    filter_upwards [(aemeasurable_quantile hSm hS).ae_eq_mk] with x hx
    rw [quantileMk, ← hx]
  rw [integral_congr_ae hae, ← integral_restrict_eq_quantile hSm hS (hg.meas.pow_const 2),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [hg.supp x hx]; ring

/-- Pair integrals of the transport are pair integrals of `g ∘ G` on `(0, L)²`. -/
theorem integral_pair_transport (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) (k : ℝ → ℝ) :
    ∫ p : ℝ × ℝ, transport hSm hS g p.1 * transport hSm hS g p.2 * k |p.1 - p.2| =
      ∫ p, g (quantile S p.1) * g (quantile S p.2) * k |p.1 - p.2|
        ∂((volume.restrict (Ioo 0 (volume S).toReal)).prod
          (volume.restrict (Ioo 0 (volume S).toReal))) := by
  rw [integral_pair_eq_restrict (A := Ioo 0 (volume S).toReal) (h := transport hSm hS g)
    (fun x hx => Set.indicator_of_notMem hx _)]
  refine integral_congr_ae ?_
  filter_upwards [ae_prod_quantile_eq_mk hSm hS] with p hp
  unfold transport
  rw [Set.indicator_of_mem hp.2.2.1, Set.indicator_of_mem hp.2.2.2, quantileMk, hp.1, hp.2.1]

/-- **Decreasing bounded kernels**: the pair energy does not decrease under transport. -/
theorem integral_pair_le_transport (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) (hg : BddSupp S g C)
    (hg0 : ∀ x, 0 ≤ g x) {k : ℝ → ℝ} (hk : Measurable k) (hk0 : ∀ r, 0 ≤ k r) {K : ℝ}
    (hkK : ∀ r, k r ≤ K) (hanti : AntitoneOn k (Ici 0)) :
    ∫ p : ℝ × ℝ, g p.1 * g p.2 * k |p.1 - p.2| ≤
      ∫ p : ℝ × ℝ, transport hSm hS g p.1 * transport hSm hS g p.2 * k |p.1 - p.2| := by
  rw [integral_pair_eq_restrict hg.supp, integral_pair_transport hSm hS]
  exact integral_kernel_le_quantile hSm hS hg.meas hg0 (fun x => (le_abs_self _).trans (hg.bound x))
    hk hk0 hkK hanti

/-- **Increasing bounded kernels**: the pair energy does not increase under transport. -/
theorem integral_pair_transport_le (hSm : MeasurableSet S) (hS : volume S ≠ ⊤) (hg : BddSupp S g C)
    (hg0 : ∀ x, 0 ≤ g x) {k : ℝ → ℝ} (hk : Measurable k) (hk0 : ∀ r, 0 ≤ k r) {K : ℝ}
    (hkK : ∀ r, k r ≤ K) (hmono : MonotoneOn k (Ici 0)) :
    ∫ p : ℝ × ℝ, transport hSm hS g p.1 * transport hSm hS g p.2 * k |p.1 - p.2| ≤
      ∫ p : ℝ × ℝ, g p.1 * g p.2 * k |p.1 - p.2| := by
  rw [integral_pair_eq_restrict hg.supp, integral_pair_transport hSm hS]
  exact integral_quantile_le_kernel hSm hS hg.meas hg0 (fun x => (le_abs_self _).trans (hg.bound x))
    hk hk0 hkK hmono

end Transport

/-! ### Unbounded kernels: monotone truncation -/

section Energies

variable {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} {κ : ℝ → ℝ}

private theorem iSup_ofReal_min_mul {a D : ℝ} (hD : 0 ≤ D) :
    ⨆ n : ℕ, ENNReal.ofReal (min a n * D) = ENNReal.ofReal (a * D) := by
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hD)) ?_
  obtain ⟨n, hn⟩ := exists_nat_ge a
  exact le_iSup_of_le n (by rw [min_eq_left hn])

private theorem monotone_ofReal_min_mul {a D : ℝ} (hD : 0 ≤ D) :
    Monotone fun n : ℕ => ENNReal.ofReal (min a n * D) := fun m n hmn =>
  ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (min_le_min_left _ (by exact_mod_cast hmn)) hD)

/-- The truncated kernel: `min(κ, n)` on `(0, ∞)` and `n` elsewhere. -/
def truncKernel (κ : ℝ → ℝ) (n : ℕ) (r : ℝ) : ℝ := if 0 < r then min (κ r) n else n

theorem measurable_truncKernel (hκ : Measurable κ) (n : ℕ) : Measurable (truncKernel κ n) :=
  Measurable.ite measurableSet_Ioi (hκ.min measurable_const) measurable_const

theorem truncKernel_nonneg (hκ0 : ∀ r, 0 ≤ κ r) (n : ℕ) (r : ℝ) : 0 ≤ truncKernel κ n r := by
  unfold truncKernel; split_ifs
  · exact le_min (hκ0 r) n.cast_nonneg
  · exact n.cast_nonneg

theorem truncKernel_le (n : ℕ) (r : ℝ) : truncKernel κ n r ≤ n := by
  unfold truncKernel; split_ifs
  · exact min_le_right _ _
  · exact le_rfl

theorem antitoneOn_truncKernel (hanti : AntitoneOn κ (Ioi 0)) (n : ℕ) :
    AntitoneOn (truncKernel κ n) (Ici 0) := by
  intro a ha b hb hab
  unfold truncKernel
  rcases eq_or_lt_of_le (mem_Ici.mp ha) with h0 | hapos
  · subst h0
    simp only [lt_irrefl, if_false]
    split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  · have hbpos : 0 < b := hapos.trans_le hab
    simp only [hapos, hbpos, if_true]
    exact min_le_min_right _ (hanti hapos hbpos hab)

/-- The jump integrand `D_h(x) = ∫ (h(u) − h(u+x))²` is measurable in `x`. -/
theorem measurable_jump (hh : BddSupp A h C) :
    Measurable fun x => ∫ u, (h u - h (u + x)) ^ 2 := by
  have hm : StronglyMeasurable (Function.uncurry fun x u : ℝ => (h u - h (u + x)) ^ 2) :=
    (((hh.meas.comp measurable_snd).sub
      (hh.meas.comp (measurable_snd.add measurable_fst))).pow_const 2).stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume)).measurable

theorem jump_le (hh : BddSupp A h C) (x : ℝ) :
    ∫ u, (h u - h (u + x)) ^ 2 ≤ 4 * ∫ u, h u ^ 2 := by
  have h1 := hh.integrable_sq
  have h2 : Integrable fun u => h (u + x) ^ 2 := h1.comp_add_right x
  calc ∫ u, (h u - h (u + x)) ^ 2 ≤ ∫ u, (2 * h u ^ 2 + 2 * h (u + x) ^ 2) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          ((h1.const_mul 2).add (h2.const_mul 2)) (ae_of_all _ fun u => ?_)
        nlinarith [sq_nonneg (h u + h (u + x))]
    _ = 4 * ∫ u, h u ^ 2 := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul,
          integral_add_right_eq_self (fun u => h u ^ 2) x]
        ring

/-- **Truncated jump energy in pair form.** -/
theorem integral_truncJump (hh : BddSupp A h C) (hκ : Measurable κ) (hκ0 : ∀ r, 0 ≤ κ r)
    {n : ℕ} (hint : IntegrableOn (fun x => min (κ x) n) (Ioi 0)) :
    ∫ x in Ioi 0, min (κ x) n * ∫ u, (h u - h (u + x)) ^ 2 =
      2 * (∫ u, h u ^ 2) * (∫ x in Ioi 0, min (κ x) n) -
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * truncKernel κ n |p.1 - p.2| := by
  have hkK : ∀ r, |truncKernel κ n r| ≤ n := fun r => by
    rw [abs_of_nonneg (truncKernel_nonneg hκ0 n r)]; exact truncKernel_le n r
  rw [integral_pair_eq_two_mul_Ioi hh (measurable_truncKernel hκ n) hkK]
  have hcI : IntegrableOn (fun x => truncKernel κ n x * autocorr h x) (Ioi 0) := by
    refine (integrable_kernel_mul_autocorr hh (measurable_truncKernel hκ n) hkK).integrableOn.congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp only [abs_of_pos (mem_Ioi.mp hx)]
  have e1 : EqOn (fun x => min (κ x) n * ∫ u, (h u - h (u + x)) ^ 2)
      (fun x => 2 * (∫ u, h u ^ 2) * min (κ x) n - 2 * (truncKernel κ n x * autocorr h x))
      (Ioi 0) := fun x hx => by
    simp only
    rw [integral_jump_sq hh x, truncKernel, if_pos (mem_Ioi.mp hx)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi e1,
    integral_sub (hint.const_mul _) (hcI.const_mul 2), integral_const_mul, integral_const_mul]

/-- **Jump energy as a supremum of truncated pair forms.** -/
theorem lintegral_jump_eq_iSup (hh : BddSupp A h C) (hκ : Measurable κ) (hκ0 : ∀ r, 0 ≤ κ r)
    (hint : ∀ n : ℕ, IntegrableOn (fun x => min (κ x) n) (Ioi 0)) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal (κ x * ∫ u, (h u - h (u + x)) ^ 2) =
      ⨆ n : ℕ, ENNReal.ofReal (2 * (∫ u, h u ^ 2) * (∫ x in Ioi 0, min (κ x) n) -
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * truncKernel κ n |p.1 - p.2|) := by
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hDm := measurable_jump hh
  have e : (fun x => ENNReal.ofReal (κ x * ∫ u, (h u - h (u + x)) ^ 2)) =
      fun x => ⨆ n : ℕ, ENNReal.ofReal (min (κ x) n * ∫ u, (h u - h (u + x)) ^ 2) := by
    funext x; rw [iSup_ofReal_min_mul (hD0 x)]
  have hmeas : ∀ n : ℕ, Measurable fun x =>
      ENNReal.ofReal (min (κ x) n * ∫ u, (h u - h (u + x)) ^ 2) :=
    fun n => ((hκ.min measurable_const).mul hDm).ennreal_ofReal
  rw [e, lintegral_iSup hmeas (fun m n hmn x => monotone_ofReal_min_mul (hD0 x) hmn)]
  congr 1
  funext n
  have hI : IntegrableOn (fun x => min (κ x) n * ∫ u, (h u - h (u + x)) ^ 2) (Ioi 0) := by
    refine ((hint n).mul_const (4 * ∫ u, h u ^ 2)).mono'
      ((hκ.min measurable_const).mul hDm).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_min (hκ0 x) n.cast_nonneg) (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) (le_min (hκ0 x) n.cast_nonneg)
  rw [← integral_truncJump hh hκ hκ0 (hint n), ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun x => mul_nonneg (le_min (hκ0 x) n.cast_nonneg) (hD0 x))]

/-- **Pair energy as a supremum of truncated pair forms**, for `h ≥ 0`. -/
theorem lintegral_pair_eq_iSup (hh : BddSupp A h C) (hh0 : ∀ x, 0 ≤ h x) (hκ : Measurable κ)
    (hκ0 : ∀ r, 0 ≤ κ r) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (h p.1 * h p.2 * κ |p.1 - p.2|) =
      ⨆ n : ℕ, ENNReal.ofReal (∫ p : ℝ × ℝ, h p.1 * h p.2 * min (κ |p.1 - p.2|) n) := by
  have hP0 : ∀ p : ℝ × ℝ, 0 ≤ h p.1 * h p.2 := fun p => mul_nonneg (hh0 _) (hh0 _)
  have hPm : Measurable fun p : ℝ × ℝ => h p.1 * h p.2 :=
    (hh.meas.comp measurable_fst).mul (hh.meas.comp measurable_snd)
  have hkm : Measurable fun p : ℝ × ℝ => κ |p.1 - p.2| :=
    hκ.comp (measurable_fst.sub measurable_snd).abs
  have e : (fun p : ℝ × ℝ => ENNReal.ofReal (h p.1 * h p.2 * κ |p.1 - p.2|)) =
      fun p => ⨆ n : ℕ, ENNReal.ofReal (h p.1 * h p.2 * min (κ |p.1 - p.2|) n) := by
    funext p
    simp_rw [mul_comm (h p.1 * h p.2)]
    rw [iSup_ofReal_min_mul (hP0 p)]
  have hmeas : ∀ n : ℕ, Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (h p.1 * h p.2 * min (κ |p.1 - p.2|) n) :=
    fun n => (hPm.mul (hkm.min measurable_const)).ennreal_ofReal
  have hmono : ∀ p : ℝ × ℝ, Monotone fun n : ℕ =>
      ENNReal.ofReal (h p.1 * h p.2 * min (κ |p.1 - p.2|) n) := fun p m n hmn => by
    simp_rw [mul_comm (h p.1 * h p.2)]
    exact monotone_ofReal_min_mul (hP0 p) hmn
  rw [e, lintegral_iSup hmeas (fun m n hmn p => hmono p hmn)]
  congr 1
  funext n
  have hI : Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * min (κ |p.1 - p.2|) n) := by
    rw [Measure.volume_eq_prod]
    refine ((hh.integrable.abs.mul_prod hh.integrable.abs).mul_const (n : ℝ)).mono'
      (hPm.mul (hkm.min measurable_const)).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_min (hκ0 _) n.cast_nonneg)]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun p => mul_nonneg (hP0 p)
    (le_min (hκ0 _) n.cast_nonneg))]

end Energies

/-! ### Rearrangement inequalities for the energies -/

section Rearrangement

variable {S : Set ℝ} {g : ℝ → ℝ} {C : ℝ} {κ : ℝ → ℝ}

/-- **Jump energy does not increase under quantile transport.** For a nonnegative measurable
kernel `κ`, decreasing on `(0, ∞)` with `min(κ, n)` integrable there,
`∫_{x>0} κ(x) ∫ (g*(u) − g*(u+x))² ≤ ∫_{x>0} κ(x) ∫ (g(u) − g(u+x))²`. -/
theorem lintegral_jump_transport_le (hSm : MeasurableSet S) (hS : volume S ≠ ⊤)
    (hg : BddSupp S g C) (hg0 : ∀ x, 0 ≤ g x) (hκ : Measurable κ) (hκ0 : ∀ r, 0 ≤ κ r)
    (hanti : AntitoneOn κ (Ioi 0)) (hint : ∀ n : ℕ, IntegrableOn (fun x => min (κ x) n) (Ioi 0)) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal
        (κ x * ∫ u, (transport hSm hS g u - transport hSm hS g (u + x)) ^ 2) ≤
      ∫⁻ x in Ioi 0, ENNReal.ofReal (κ x * ∫ u, (g u - g (u + x)) ^ 2) := by
  rw [lintegral_jump_eq_iSup (transport_bddSupp hSm hS hg) hκ hκ0 hint,
    lintegral_jump_eq_iSup hg hκ hκ0 hint, integral_sq_transport hSm hS hg]
  refine iSup_mono fun n => ENNReal.ofReal_le_ofReal ?_
  have := integral_pair_le_transport hSm hS hg hg0 (measurable_truncKernel hκ n)
    (truncKernel_nonneg hκ0 n) (truncKernel_le n) (antitoneOn_truncKernel hanti n)
  linarith

/-- **Pair energy against an increasing kernel does not increase under quantile transport.** -/
theorem lintegral_pair_transport_le (hSm : MeasurableSet S) (hS : volume S ≠ ⊤)
    (hg : BddSupp S g C) (hg0 : ∀ x, 0 ≤ g x) (hκ : Measurable κ) (hκ0 : ∀ r, 0 ≤ κ r)
    (hmono : MonotoneOn κ (Ici 0)) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal
        (transport hSm hS g p.1 * transport hSm hS g p.2 * κ |p.1 - p.2|) ≤
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (g p.1 * g p.2 * κ |p.1 - p.2|) := by
  rw [lintegral_pair_eq_iSup (transport_bddSupp hSm hS hg) (transport_nonneg hSm hS hg0) hκ hκ0,
    lintegral_pair_eq_iSup hg hg0 hκ hκ0]
  refine iSup_mono fun n => ENNReal.ofReal_le_ofReal ?_
  exact integral_pair_transport_le hSm hS hg hg0 (k := fun r => min (κ r) n)
    (hκ.min measurable_const) (fun r => le_min (hκ0 r) n.cast_nonneg) (fun r => min_le_right _ _)
    (fun a ha b hb hab => min_le_min_right _ (hmono ha hb hab))

end Rearrangement

end QuantileTransport

end

end GaloisForLFunctions.HTGeometry
