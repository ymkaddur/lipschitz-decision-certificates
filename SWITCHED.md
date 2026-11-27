# State-dependent switching on observation fibers

For each action a, suppose view(act(a,x)) is known from view(x). After a controller selects an action from the hidden state, a single projected step exists precisely when the selected action outputs agree on each fiber. Two different selectors can give the same output, so requiring equality of their indices is stronger than necessary. The proof constructs the reduced step by choosing a representative for each nonempty fiber. Computing those representatives and selectors efficiently is an additional obligation.

Two individually valid bit operations, identity and negation, switch on a hidden bit and violate this criterion. In a metric space the triangle inequality separates the fixed-action Lipschitz propagation term from the discrepancy of the two actions at the same input.
