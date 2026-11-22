import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleWeights
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Winding coordinates for sampled relative clocks

A stationary word has an integer energy winding on every active edge.
The windings determine all relative energies in each connected component.
One minimum label per component fixes the remaining additive constants.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open CopyExchange
open scoped Classical

variable {I E : Type*}

/-- Each edge compares its two endpoint energies at its own real sampling time. -/
structure Network (I E : Type*) where
  src : E → I
  dst : E → I
  time : E → ℝ

namespace Network

variable (G : Network I E)

abbrev Active := {e : E // G.time e ≠ 0}

def phase (e : E) (x : I → ℕ+) : Circle :=
  Circle.exp (G.time e * (energy (x (G.src e)) - energy (x (G.dst e))))

def Resonant (x : I → ℕ+) : Prop := ∀ e, G.phase e x = 1

abbrev Word := {x : I → ℕ+ // G.Resonant x}

def Component := Quot (fun i j : I => ∃ e : G.Active, G.src e = i ∧ G.dst e = j)

def component (i : I) : G.Component := Quot.mk _ i

theorem component_surjective : Function.Surjective G.component := fun c => Quot.exists_rep c

theorem component_edge (e : G.Active) : G.component (G.src e) = G.component (G.dst e) :=
  Quot.sound (show ∃ a : G.Active, G.src a = G.src e ∧ G.dst a = G.dst e from ⟨e,rfl,rfl⟩)

instance [Fintype I] : Fintype G.Component :=
  @Fintype.ofFinite _ (Finite.of_surjective _ G.component_surjective)

def size [Fintype I] (c : G.Component) := Fintype.card {i : I // G.component i = c}

theorem size_pos [Fintype I] (c : G.Component) : 0 < G.size c := by
  obtain ⟨i,hi⟩ := G.component_surjective c
  exact Fintype.card_pos_iff.mpr ⟨⟨i,hi⟩⟩

/-- Component-constant words always remain stationary, at all edge times. -/
def flat (u : G.Component → ℕ+) : G.Word :=
  ⟨fun i => u (G.component i),by
    intro e
    by_cases h : G.time e = 0
    · simp [phase,h]
    · simp [phase,G.component_edge ⟨e,h⟩]⟩

theorem flat_injective : Function.Injective G.flat := by
  intro a b h
  funext c
  obtain ⟨i,rfl⟩ := G.component_surjective c
  exact congrArg (fun x : G.Word => x.val i) h

theorem flat_heat [Fintype I] (s : ℂ) (u : G.Component → ℕ+) :
    wordHeat s (G.flat u).val = ∏ c, heat ((G.size c : ℂ)*s) (u c) := by
  change (∏ i, heat s (u (G.component i))) = _
  rw [← Fintype.prod_fiberwise' G.component (fun c => heat s (u c))]
  simp only [Finset.prod_const,Finset.card_univ,size,heat_nat_mul]

private theorem exists_winding (x : G.Word) (e : G.Active) :
    ∃ k : ℤ, G.time e * (energy (x.val (G.src e)) - energy (x.val (G.dst e))) = k * (2*Real.pi) :=
  Circle.exp_eq_one.mp (x.property e)

def winding (x : G.Word) (e : G.Active) : ℤ := (G.exists_winding x e).choose

theorem winding_eq (x : G.Word) (e : G.Active) :
    energy (x.val (G.src e)) - energy (x.val (G.dst e)) = (G.winding x e : ℝ) * (2*Real.pi/G.time e) := by
  have h := (G.exists_winding x e).choose_spec
  change G.time e * _ = (G.winding x e : ℝ) * _ at h
  field_simp [e.property]
  linarith only [h]

private theorem exists_lowest [Fintype I] (x : I → ℕ+) (c : G.Component) :
    ∃ j : {i : I // G.component i = c}, ∀ i : {i : I // G.component i = c}, energy (x j) ≤ energy (x i) := by
  obtain ⟨a,ha⟩ := G.component_surjective c
  have hn : (Finset.univ : Finset {i : I // G.component i = c}).Nonempty := ⟨⟨a,ha⟩,Finset.mem_univ _⟩
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ (fun i : {i : I // G.component i = c} => energy (x i)) hn
  exact ⟨j,fun i => hj i (Finset.mem_univ _)⟩

def lowestSite [Fintype I] (x : I → ℕ+) (c : G.Component) : {i : I // G.component i = c} :=
  (G.exists_lowest x c).choose

def lowest [Fintype I] (x : I → ℕ+) (c : G.Component) : ℕ+ := x (G.lowestSite x c)

theorem lowest_le [Fintype I] (x : I → ℕ+) (i : I) :
    energy (G.lowest x (G.component i)) ≤ energy (x i) :=
  (G.exists_lowest x (G.component i)).choose_spec ⟨i,rfl⟩

/-- Integer edge windings and one minimum integer label per active component. -/
def coordinates [Fintype I] (x : G.Word) := (G.lowest x.val, G.winding x)

private theorem energy_injective : Function.Injective energy := by
  intro a b h
  have he := congrArg Real.exp h
  rw [energy,energy,Real.exp_log (Nat.cast_pos.mpr a.pos),Real.exp_log (Nat.cast_pos.mpr b.pos)] at he
  exact PNat.coe_injective (Nat.cast_injective (R := ℝ) he)

theorem coordinates_injective [Fintype I] : Function.Injective G.coordinates := by
  intro x y h
  have hlow : G.lowest x.val = G.lowest y.val := congrArg Prod.fst h
  have hw : G.winding x = G.winding y := congrArg Prod.snd h
  let diff (i : I) := energy (x.val i) - energy (y.val i)
  let d : G.Component → ℝ := Quot.lift diff (by
    rintro _ _ ⟨e,rfl,rfl⟩
    have hx := G.winding_eq x e
    have hy := G.winding_eq y e
    rw [hw] at hx
    dsimp [diff]
    linarith only [hx,hy])
  have hd (i : I) : d (G.component i) = energy (x.val i) - energy (y.val i) := rfl
  have hz (c : G.Component) : d c = 0 := by
    let i := G.lowestSite x.val c
    let j := G.lowestSite y.val c
    have hxi := hd i.val
    have hyj := hd j.val
    rw [i.property] at hxi
    rw [j.property] at hyj
    have hi := G.lowest_le y.val i.val
    have hj := G.lowest_le x.val j.val
    rw [i.property] at hi
    rw [j.property,hlow] at hj
    change d c = energy (G.lowest x.val c) - _ at hxi
    change d c = _ - energy (G.lowest y.val c) at hyj
    rw [hlow] at hxi
    linarith only [hxi,hyj,hi,hj]
  apply Subtype.ext
  funext i
  apply energy_injective
  exact sub_eq_zero.mp ((hd i).symm.trans (hz (G.component i)))

#print axioms flat_heat
#print axioms winding_eq
#print axioms coordinates_injective

end Network
end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
