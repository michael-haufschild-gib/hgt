import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.NetworkSummability
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.HeatSectors
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting
import GaloisForLFunctions.HTGeometry.WeightedAtomHilbert

/-!
# The trace boundary of sampled relative clocks

The accepted labels span exactly the joint fixed vectors of the sampled
unitaries. A single edge at any nonzero time gives the same critical-line
criterion for binary probability conservation.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open CopyExchange HTGeometry
open scoped Classical

variable {I E : Type*}

namespace Network

variable (G : Network I E)

/-- The relative Hamiltonian time unitary on the entire tuple space. -/
def tick (e : E) : LabelSpace (I → ℕ+) ≃ₗᵢ[ℂ] LabelSpace (I → ℕ+) :=
  lpPhaseUnitary (fun x => (G.phase e x : ℂ)) (fun _ => Circle.norm_coe _)

theorem joint_fixed_iff [Fintype I] (f : LabelSpace (I → ℕ+)) :
    (∀ e, G.tick e f = f) ↔ f ∈ Sector G.Resonant := by
  rw [sector_mem]
  constructor
  · intro h x hx
    by_contra hn
    apply hx
    intro e
    have he := congrArg (fun v : LabelSpace (I → ℕ+) => v x) (h e)
    change (G.phase e x : ℂ) * f x = f x at he
    apply Subtype.ext
    exact mul_right_cancel₀ hn (he.trans (one_mul (f x)).symm)
  · intro h e
    apply lp.ext
    funext x
    change (G.phase e x : ℂ) * f x = f x
    by_cases hx : G.Resonant x
    · rw [hx e,Circle.coe_one,one_mul]
    · rw [h x hx,mul_zero]

theorem traceClass_iff [Fintype I] [Fintype E] (s : ℂ) : HasSectorHeat G.Resonant s ↔ G.Domain s :=
  (sectorHeat_iff G.Resonant s).trans (G.summable_iff s)

theorem empty_trace [Fintype I] [IsEmpty I] (s : {z : ℂ // AbsoluteHeat G.Resonant z}) :
    ContinuousLinearMap.opTrace (sectorHeat G.Resonant s) = 1 := by
  letI : Unique G.Word := ⟨⟨G.flat (fun _ => 1)⟩,fun _ => Subsingleton.elim _ _⟩
  rw [sectorHeat_trace,tsum_eq_single (default : G.Word) (fun b hb => (hb (Subsingleton.elim b _)).elim)]
  simp [wordHeat]

def sizes [Fintype I] := Finset.univ.image G.size

private theorem sizes_nonempty [Fintype I] [Nonempty I] : G.sizes.Nonempty :=
  ⟨_,Finset.mem_image.mpr ⟨G.component (Classical.arbitrary I),Finset.mem_univ _,rfl⟩⟩

def smallest [Fintype I] [Nonempty I] : ℕ := G.sizes.min' (G.sizes_nonempty)

private theorem hits_smallest [Fintype I] [Nonempty I] : ∃ c, G.size c = G.smallest := by
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp (Finset.min'_mem _ G.sizes_nonempty)
  exact ⟨c,hc⟩

private theorem smallest_le [Fintype I] [Nonempty I] (c : G.Component) : G.smallest ≤ G.size c :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩)

theorem domain_smallest [Fintype I] [Nonempty I] (s : ℂ) :
    G.Domain s ↔ 1/(G.smallest : ℝ) < s.re := by
  obtain ⟨c,hc⟩ := G.hits_smallest
  have hp : 0 < (G.smallest : ℝ) := by rw [← hc]; exact_mod_cast G.size_pos c
  rw [div_lt_iff₀ hp,mul_comm s.re]
  constructor
  · intro h
    simpa only [← hc] using h c
  · intro h j
    have hs : 0 < s.re := by
      by_contra! hn
      linarith only [mul_nonpos_of_nonneg_of_nonpos hp.le hn,h]
    have hj : (G.smallest : ℝ) ≤ G.size j := by exact_mod_cast G.smallest_le j
    exact h.trans_le (mul_le_mul_of_nonneg_right hj hs.le)

/-- With no active comparisons each site forms its own component. -/
theorem size_of_no_active [Fintype I] [IsEmpty G.Active] (c : G.Component) : G.size c = 1 := by
  let read : G.Component → I := Quot.lift id (by
    rintro _ _ ⟨e,_,_⟩
    exact isEmptyElim e)
  have hi : Function.Injective G.component := fun _ _ h => congrArg read h
  obtain ⟨i,rfl⟩ := G.component_surjective c
  exact Fintype.card_eq_one_iff.mpr ⟨⟨i,rfl⟩,fun j => Subtype.ext (hi j.property)⟩

end Network

/-- One physical comparison between two copies. -/
def binary (t : ℝ) : Network Bool Unit := ⟨fun _ => false,fun _ => true,fun _ => t⟩

private theorem binary_size_live {t : ℝ} (ht : t ≠ 0) (c : (binary t).Component) : (binary t).size c = 2 := by
  let G := binary t
  have he : G.component false = G.component true := G.component_edge ⟨(),ht⟩
  have hc (i : Bool) : G.component i = c := by
    obtain ⟨j,rfl⟩ := G.component_surjective c
    cases i <;> cases j
    · rfl
    · exact he
    · exact he.symm
    · rfl
  let e : {i : Bool // G.component i = c} ≃ Bool :=
    ⟨Subtype.val,fun i => ⟨i,hc i⟩,fun _ => rfl,fun _ => rfl⟩
  exact (Fintype.card_congr e).trans Fintype.card_bool

private theorem binary_size_zero (c : (binary 0).Component) : (binary 0).size c = 1 := by
  letI : IsEmpty (binary 0).Active := ⟨fun e => e.property rfl⟩
  exact (binary 0).size_of_no_active c

theorem binary_threshold (t : ℝ) (s : ℂ) :
    HasSectorHeat (binary t).Resonant s ↔ (if t = 0 then 1 else (1/2 : ℝ)) < s.re := by
  rw [Network.traceClass_iff,Network.domain_smallest]
  obtain ⟨c,hc⟩ := (binary t).hits_smallest
  rw [← hc]
  by_cases h : t = 0
  · subst t
    rw [binary_size_zero]
    norm_num
  · rw [binary_size_live h,if_neg h]
    norm_num

/-- Even resonant nonzero sampling times recover the isometry line as a trace-class boundary. -/
theorem sampled_clock_split_iff (t : {t : ℝ // t ≠ 0}) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      (¬HasSectorHeat (binary t.val).Resonant s ∧
        ∀ δ : ℝ, 0 < δ → HasSectorHeat (binary t.val).Resonant (s+(δ : ℂ))) := by
  simp only [split_isometric_iff,binary_threshold,if_neg t.property,not_lt,Complex.add_re,Complex.ofReal_re]
  constructor
  · intro h
    exact ⟨h.le,fun δ hδ => by linarith only [h,hδ]⟩
  · rintro ⟨hl,hr⟩
    apply le_antisymm hl
    by_contra! h
    have hh := hr _ (sub_pos.mpr h)
    linarith only [hh]

#print axioms Network.joint_fixed_iff
#print axioms Network.traceClass_iff
#print axioms Network.empty_trace
#print axioms Network.domain_smallest
#print axioms binary_threshold
#print axioms sampled_clock_split_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
