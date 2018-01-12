import sys, os
sys.path.append(os.path.split(os.path.split(os.path.realpath(__file__))[0])[0])

from learn.dsloader import *
from learn.embedding import sentence_len, word_size

from keras import backend as K
from keras.models import Sequential
from keras.layers import Dense, Activation, Dropout, SimpleRNN as LSTM

import gc

_epochs = 20
_num_train = None
_num_test = None
_batch_size = 50
_dropout = 0.5

_num_lstm_layers = 4
_num_hidden = 1024

mode = 'reoonly'

if mode == 'reoonly':
    train_set_X, train_set_Y = load_dataset('reo_ds.txt', _num_train)
    test_set_X = train_set_X[-20:]
    test_set_Y = train_set_Y[-20:]
    train_set_X = train_set_X[:-20]
    train_set_Y = train_set_Y[:-20]

    _num_hidden = 1024
    _num_lstm_layers = 2

    _batch_size = 15
    _epochs = 30
elif mode == 'coqonly':
    _num_train = 2000

    train_set_X, train_set_Y = load_dataset('raw_ds.txt', _num_train)
    test_set_X = train_set_X[-500:]
    test_set_Y = train_set_Y[-500:]
    train_set_X = train_set_X[:-500]
    train_set_Y = train_set_Y[:-500]

    _batch_size = 50
    _epochs = 15
else:
    train_set_X, train_set_Y = load_dataset('raw_ds.txt', _num_train)
    test_set_X, test_set_Y = load_dataset('reo_ds.txt', _num_test)

print("data analyzing done.")

lstm_word_width = sentence_len * word_size
lstm_time_step = time_step
lstmlayers = 4

correctness_all = []
loss_all = []

average_rounds = 10

for r in range(average_rounds):
    gc.collect()
    model = Sequential()
    for _ in range(1, _num_lstm_layers):
        model.add(LSTM(
            _num_hidden,
            input_shape=(lstm_time_step, lstm_word_width),
            return_sequences=True
        ))
        # model.add(Dropout(_dropout))

    model.add(LSTM(_num_hidden, input_shape=(lstm_time_step, lstm_word_width)))
    model.add(Dropout(_dropout))

    model.add(Dense(len(supported_tactics)))
    model.add(Activation('softmax'))
    model.compile(loss='categorical_crossentropy', optimizer='rmsprop')

    print(model.input_shape)
    print("keras model built. start training")

    print("Round %d" % r)
    for e in range(_epochs):
        print("Epoch %d" % e)
        try:
            history = model.fit(train_set_X, train_set_Y, batch_size=_batch_size, epochs=1)
            if e >= len(loss_all):
                loss_all.append(history.history['loss'][0])
            else:
                loss_all[e] += history.history['loss'][0]
            test_result = model.predict(test_set_X)
            target_result = [list(line).index(max(line)) for line in test_set_Y]

            correctness_epoch = []

            for i in range(1, 6):
                # verify
                test_result_n = [get_maximum_indexes(line, i) for line in test_result]
                target_result = [list(line).index(max(line)) for line in test_set_Y]

                correctness = float(sum([1 if target_result[j] in test_result_n[j] else 0 for j in range(len(target_result))])) / len(target_result)
                print("CORRECTNESS when selecting %d tactics: %.2f percents" % (i, correctness * 100))

                correctness_epoch.append(correctness)

            if e >= len(correctness_all):
                correctness_all.append(correctness_epoch)
            else:
                for i in range(5):
                    correctness_all[e][i] += correctness_epoch[i]
        except KeyboardInterrupt:
            break

# used for drawing graphs in latex/pgfplots
for i in range(3):
    line = "\\addplot+[smooth] coordinates \n{"
    for j in range(len(correctness_all)):
        correctness_all[j][i] /= average_rounds
        line += "(%d, %f) " % (j + 1, correctness_all[j][i])

    line += "};\n"
    print(line, "\n")

line = "\\addplot+[smooth] coordinates \n{"
for j in range(len(loss_all)):
    loss_all[j] /= average_rounds
    line += "(%d, %f) " % (j + 1 , loss_all[j])

line += "};\n"
print(line, "\n")