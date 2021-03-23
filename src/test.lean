import algebra.punit_instances

example : add_group punit := infer_instance

@[to_additive foo']
def foo {G : Type*} [group G] : G ≃* punit := sorry
